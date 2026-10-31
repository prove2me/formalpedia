-- Prove2me | Theorems.Thm_GhostPenalty_lemma_2
-- name    : GhostPenalty.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:56.190472+00:00
-- url     : https://prove2.me/theorems/2e11de38-fed6-45be-8224-63a38c0a5388
-- title:
--   Lemma 2 — Slater point, ES point, or FJ point at every $\hat x\in K$
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Let $\hat x\in K$. Then:
--
--   1. if $\max_i\{g_i(\hat x)_+\}>0$ and $\kappa(\hat x)<\max_i\{g_i(\hat x)_+\}$, there is $d\in\operatorname{int}(\beta\mathbb B^n_\infty)\cap\operatorname{relint}(K-\hat x)$ with $\tilde g(d;\hat x)<\kappa(\hat x)e$;
--   2. if $\max_i\{g_i(\hat x)_+\}>0$ and $\kappa(\hat x)=\max_i\{g_i(\hat x)_+\}$, then $\hat x$ is an ES point for (P);
--   3. if $\max_i\{g_i(\hat x)_+\}=0$, then either $\hat x$ is an FJ point for (P), or there is $d\in\operatorname{int}(\beta\mathbb B^n_\infty)\cap\operatorname{relint}(K-\hat x)$ with $\tilde g(d;\hat x)<0$.
--
--   The source's "for all $\rho\in(0,\beta)$" refers to the parameter $\rho$ of $\kappa$, which is arbitrary in $(0,\beta)$ here. The three cases are exhaustive since $\kappa(\hat x)\le\max_i\{g_i(\hat x)_+\}$.
--
--   **Formalization Note** $\operatorname{relint}$ is Mathlib's `intrinsicInterior`; vector inequalities are componentwise.
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - reading: "for all ρ ∈ (0,β)" inside the conclusions of (i) and (iii) → ρ is the universally quantified parameter of κ, one binder for the whole lemma; reason: the conclusions mention ρ only through κ, and the proof takes the ρ of κ; (iii)'s conclusion does not depend on ρ
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Lemma 2, p.10

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_kappa
import Definitions.Def_GhostPenalty_IsFJ
import Definitions.Def_GhostPenalty_IsES

namespace GhostPenalty

/-- **Lemma 2: the three cases at a point of `K`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Lemma 2, p.10: "Under Assumption A, the following results hold for any `x̂ ∈ K`:
(i) if `max_i{g_i(x̂)+} > 0` and `κ(x̂) < max_i{g_i(x̂)+}`, then, for all `ρ ∈ (0,β)`, there exists
`d ∈ int(βBⁿ∞) ∩ relint(K − x̂)` such that `g̃(d; x̂) < κ(x̂)e`;
(ii) if `max_i{g_i(x̂)+} > 0` and `κ(x̂) = max_i{g_i(x̂)+}`, then `x̂` is an ES point for (P);
(iii) if `max_i{g_i(x̂)+} = 0`, then either `x̂` is a FJ point for (P) or, for all `ρ ∈ (0,β)`,
there exists `d ∈ int(βBⁿ∞) ∩ relint(K − x̂)` such that `g̃(d; x̂) < 0`."

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. The "for all `ρ ∈ (0,β)`" of the page is the universally quantified parameter `ρ` of
`κ`. `int(βBⁿ∞)` is `interior (box n β)`, `relint(K − x̂)` is `intrinsicInterior ℝ {u | x̂ + u ∈ K}`,
and vector inequalities `g̃(d;x̂) < κ(x̂)e`, `g̃(d;x̂) < 0` are componentwise. -/
theorem lemma_2 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c) (xh : EuclideanSpace ℝ (Fin n)) (hxh : xh ∈ K) :
    (0 < posMax g xh → kappa g gt K lam ρ xh < posMax g xh →
        ∃ d ∈ interior (box n β) ∩ intrinsicInterior ℝ {u | xh + u ∈ K},
          ∀ i, gt i d xh < kappa g gt K lam ρ xh) ∧
      (0 < posMax g xh → kappa g gt K lam ρ xh = posMax g xh → IsES g K xh) ∧
      (posMax g xh = 0 → IsFJ g K xh ∨
        ∃ d ∈ interior (box n β) ∩ intrinsicInterior ℝ {u | xh + u ∈ K}, ∀ i, gt i d xh < 0) := by sorry

end GhostPenalty
