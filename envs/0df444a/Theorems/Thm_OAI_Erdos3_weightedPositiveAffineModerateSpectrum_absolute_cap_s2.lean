-- Prove2me | Theorems.Thm_OAI_Erdos3_weightedPositiveAffineModerateSpectrum_absolute_cap_s2
-- name    : OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:40.937636+00:00
-- url     : https://prove2.me/theorems/5132ee93-3105-42bb-933d-4d92b1993121
-- title:
--   The total absolute size of the product of weighted affine moderate grid coefficients is bounded by the positive moderate spectrum budget plus 1
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $B$ and $I$ be finite types ($I$ with decidable equality) and $n$ a natural number. For each $b \in B$ let $c_b$ be a normalized scalar cube source over the empty index type and, for each $j \in \mathrm{Fin}(n+1)$, $s_{b,j}$ a normalized scalar cube source over $I$ (OpenAI's structure `NormalizedScalarCubeSource`: a length, a modulus bound, moduli and residues, and a Lipschitz weight normalized to mean $1$ over the residue-constrained integer cube; its `source` is the corresponding reweighted probability weights on the integer cube box, its `modulus i` are the moduli). Let $A \in \mathbb{R}_{\ge 0}$ be a Lipschitz constant of `Real.smoothTransition`, $U, V, W, L$ reals and $t$ a natural number.
--
--   **Hypotheses.** $U \ge 1$; `ScalarCubePrimitiveBudget (c b) A U` and `ScalarCubePrimitiveBudget (s b j) A U` for all $b, j$ (OpenAI's structure asserting that $U$ bounds $1$, $|I|+1$, the modulus bound, the weight bound, the weight Lipschitz constant, and several explicit geometric constants of the source); $u : B \to \mathrm{Fin}(n+1) \to \mathrm{Option}\ I \to \mathbb{R}$ and $v : B \to \mathrm{Fin}(n+1) \to \mathrm{Option}\ I \to \mathbb{N}$ with all $v_{b,j,i} > 0$ and $v_{b,j,i}\cdot(\text{modulus } i \text{ of } s_{b,j}) \le U$; for every $b$ and every point $z$ of positive weight under the source of $c_b$, $(\text{length of } c_b)/4 \le z_{\mathrm{none}}$; $V \ge 0$, $W \ge 0$, $L \ge 0$; $L \le$ length of $s_{b,j}$ for all $b, j$; $M > 0$ a natural number with
--   $$\frac{M}{(\text{length of } c_b)\cdot\prod_{j}(\text{length of } s_{b,j})} \le V \quad\text{for all } b;$$
--   $J$ a finite set of finite subsets of $I$, each of size at most $n+1$; `positiveModerateSpectrumBlockCount n |J| t` $\le |B|$; and $M^{|J|} \le W L^{t}$.
--
--   **Statement.** For a frequency index $k : J \to \mathrm{Fin}(M)$, let $\gamma_b(k)$ = `weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k`, i.e.
--   $$\gamma_b(k) = \mathbb{E}_{z \sim c_b}\ \mathbb{E}_{x \sim \prod_j s_{b,j}}\ e\Bigl(z_{\mathrm{none}}\cdot \texttt{booleanBlockPhase}\bigl(\xi_k,\ j \mapsto \texttt{affineCubeCoordinates}\ (u_{b,j})\ (v_{b,j})\ (x_j)\bigr)\Bigr),$$
--   where $e(\theta)$ is the unit-circle character of $\theta$ (`character`), $\xi_k(S) = k(S)/M$ for $S \in J$ and $0$ otherwise (`gridJetFrequency M J k`), and `booleanBlockPhase` $\xi$ $a$ $= \sum_{S} \xi(S)$ times the Boolean (Möbius) coefficient at $S$ of OpenAI's block value of $a$. Then
--   $$\sum_{k : J \to \mathrm{Fin}(M)} \Bigl| \prod_{b \in B} \gamma_b(k) \Bigr| \le \texttt{positiveModerateSpectrumCardBudget}\ n\ |J|\ t\ U\ V\ W\ 1 + 1,$$
--   where `positiveModerateSpectrumCardBudget` is an explicit real-valued budget function of OpenAI.
--
--   Lean: `OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap_s2`, which states OpenAI's `OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap` (in `lean/OAI/Combinatorics/Progressions/Fourier/FixedPrincipalCoefficientSpectrum.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B150` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/FixedPrincipalCoefficientSpectrum.lean (declaration OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerateSpectrum_absolute_cap_s2 {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
 :
    (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k‖) ≤
      positiveModerateSpectrumCardBudget n J.card t U V W 1 + 1 := by
  sorry

end Erdos3

end

end OAI
end
