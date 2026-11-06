-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_4_4
-- name    : MatrixLeeSidford.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:37:12.675228+00:00
-- url     : https://prove2.me/theorems/5a53feb6-24dc-44bb-9093-c62eb5cb34da
-- title:
--   Lemma 4.4 — existence, uniqueness, smoothness and stationarity of the optimal weight
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer. For every $y\in\Omega$:
--   1. $f_y$ has a unique minimizer $G_*=G_*(y)$ over $G\succ0$, and $G_*(y)$ depends smoothly on $y\in\Omega$;
--   2. with $W_y=L_y(G_*)^{s-1}$,
--   $$
--   L_y^*(W_y)=G_*^{-1},\qquad \operatorname{tr}\big[L_y(G_*)^s\big]=\operatorname{tr}\big[W_y^{s/(s-1)}\big]=m ;
--   $$
--   3. the potential has the dual formulation
--   $$
--   \Phi_p(y)=\frac12\max_{W\succeq0}\Big\{\log\det L_y^*(W)-\frac{s-1}{s}\operatorname{tr}\big[W^{s/(s-1)}\big]\Big\},
--   $$
--   where the objective is $-\infty$ when $L_y^*(W)$ is singular, and $W_y$ is the unique maximizer.
--
--   The identity $\operatorname{tr}[L_y(G_*)^s]=m$ (the mass identity) is the source of the factor $m$ in the barrier parameter.
--
--   **Formalization Note** Smoothness is entrywise $C^\infty$ of $y\mapsto G_*(y)$ on $\Omega$. The $-\infty$ convention is encoded by maximizing over the $W\succeq0$ with $L_y^*(W)\succ0$: $W_y$ belongs to that set, attains $2\Phi_p(y)$, and every other member has a strictly smaller value; matrices with singular $L_y^*(W)$ have value $-\infty$ and are therefore strictly worse.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
--   - encoding: G_*(y) depends smoothly on y → each entry of y ↦ optWeightAt y is ContDiffOn ℝ ∞ on Ω; reason: smoothness of a matrix-valued map is smoothness of its entries
--   - encoding: max over W ⪰ 0 with value −∞ when L_y^*(W) is singular → W_y ⪰ 0, L_y^*(W_y) ≻ 0, Φ_p(y) = ½·value(W_y), and every W ⪰ 0 with L_y^*(W) ≻ 0 has value ≤ value(W_y) with equality only at W = W_y; reason: the excluded W have value −∞ < value(W_y), so this is the same maximum and the same unique maximizer
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 4.4, Eqs. (4.7)–(4.9), p.34

import Mathlib
import Definitions.Def_MatrixLeeSidford_optWeightAt
import Definitions.Def_MatrixLeeSidford_Wmat
import Definitions.Def_MatrixLeeSidford_Ladj
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_matRpow
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 4.4 (Existence and stationarity)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.34). Let `y ∈ Ω`. The function `f_y`
has a unique minimizer `G_* = G_*(y)` over `G ≻ 0`, and `G_*(y)` depends smoothly on `y`. With
`W_y := L_y(G_*)^{s−1}` (4.7): `L_y^*(W_y) = G_*^{-1}`, `tr[L_y(G_*)^s] = tr[W_y^{s/(s−1)}] = m` (4.8), and
`Φ_p(y) = ½ max_{W ⪰ 0} {log det L_y^*(W) − ((s−1)/s) tr[W^{s/(s−1)}]}` (4.9), the objective being `−∞`
when `L_y^*(W)` is singular, with `W_y` the unique maximizer.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. `s ≥ 2` integer. Smoothness is entrywise `C^∞` of `y ↦ G_*(y)` on
`Ω`. The `−∞` convention of (4.9) is encoded by maximizing over the `W ⪰ 0` with `L_y^*(W) ≻ 0`
(for `W ⪰ 0`, `L_y^*(W) ⪰ 0` always): `W_y` lies in that set, attains `2Φ_p(y)`, and every other
`W` of the set has a strictly smaller value; a `W` with singular `L_y^*(W)` has value `−∞`, so
`W_y` is the unique maximizer over all `W ⪰ 0`. -/
theorem lemma_4_4 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) :
    (∀ y ∈ dualRegion A C, ∃! G : Matrix (Fin m) (Fin m) ℝ, G.PosDef ∧
      ∀ G' : Matrix (Fin m) (Fin m) ℝ, G'.PosDef → fObj A (slack A C y) s G ≤ fObj A (slack A C y) s G') ∧
    (∀ y ∈ dualRegion A C, (optWeightAt A C s y).PosDef ∧
      ∀ G' : Matrix (Fin m) (Fin m) ℝ, G'.PosDef →
        fObj A (slack A C y) s (optWeightAt A C s y) ≤ fObj A (slack A C y) s G') ∧
    (∀ i j, ContDiffOn ℝ ∞ (fun y => optWeightAt A C s y i j) (dualRegion A C)) ∧
    ∀ y ∈ dualRegion A C,
      let S := slack A C y
      let G := optWeight A S s
      let W := Wmat A S s
      let D : Matrix (Fin n) (Fin n) ℝ → ℝ := fun W' =>
      Real.log (Ladj A S W').det - (((s : ℝ) - 1) / s) * (matRpow ((s : ℝ) / ((s : ℝ) - 1)) W').trace
      Ladj A S W = G⁻¹ ∧ (Lmap A S G ^ s).trace = m ∧
      (matRpow ((s : ℝ) / ((s : ℝ) - 1)) W).trace = m ∧
      W.PosSemidef ∧ (Ladj A S W).PosDef ∧ Phi A C s y = (1 / 2) * D W ∧
      ∀ W' : Matrix (Fin n) (Fin n) ℝ, W'.PosSemidef → (Ladj A S W').PosDef →
        D W' ≤ D W ∧ (D W' = D W → W' = W) := by sorry

end MatrixLeeSidford
