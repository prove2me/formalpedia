-- Prove2me | Theorems.Thm_OAI_Erdos3_weightedPositiveAffineModerate_uniform_spectrum_tail_s2
-- name    : OAI.Erdos3.weightedPositiveAffineModerate_uniform_spectrum_tail_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:37.70505+00:00
-- url     : https://prove2.me/theorems/c6df353c-a572-4cf7-ac70-227838f0dc29
-- title:
--   The tail, outside a moderate spectrum cover, of the product over blocks of weighted affine moderate grid coefficients is at most ε
-- statement:
--   Let $B$ and $I$ be finite types ($I$ with decidable equality) and $n \in \mathbb{N}$. A `NormalizedScalarCubeSource I` (a structure defined by OpenAI) consists of a positive length, a modulus bound, positive moduli $\le$ the modulus bound and residues indexed by $\mathrm{Option}\,I$, with $(|I| + 1) \cdot \text{modulus bound} \le \text{length}$, and a weight function $\omega$ on $\mathbb{R}^{\mathrm{Option}\,I}$ with values in $[0, \text{weight bound}]$ (a positive bound) that is Lipschitz with a given constant and has mean $1$ at the points $z/\text{length}$ under the residue-conditioned integer scalar cube law `scalarCubeResidueWeights` with these parameters; its law `source` is that integer law reweighted by $z \mapsto \omega(z/\text{length})$. For a source $s$, a nonnegative real $A$ and a real $U$, `ScalarCubePrimitiveBudget s A U` (defined by OpenAI) means: $1 \le U$, $|I| + 1 \le U$, and the modulus bound, the weight bound, the weight Lipschitz constant, `scalarCubeBoundaryConstant I`, $2\cdot$`scalarCubeGridBoundaryConstant I` / vol(`scalarCubeDomain I`), `scalarCubeCutoffDerivativeNumerator I A` and `paddedResidueDensityCap I (modulus bound)` are all at most $U$.
--
--   **Data and hypotheses.** Let $c_b$ ($b \in B$) be normalized scalar cube sources over the empty type and $s_{b,j}$ ($b \in B$, $j \in \mathrm{Fin}(n+1)$) normalized scalar cube sources over $I$. Let $A \in \mathbb{R}_{\ge 0}$ be a Lipschitz constant of `Real.smoothTransition`. Let $U, V, W, L, \zeta, \varepsilon$ be reals and $t \in \mathbb{N}$. Assume:
--   - $1 \le U$; `ScalarCubePrimitiveBudget (c b) A U` for all $b$ and `ScalarCubePrimitiveBudget (s b j) A U` for all $b, j$;
--   - $u_{b,j} : \mathrm{Option}\,I \to \mathbb{R}$ and $v_{b,j} : \mathrm{Option}\,I \to \mathbb{N}$ with $v_{b,j}(i) > 0$ and $v_{b,j}(i) \cdot \mathrm{modulus}(s_{b,j})(i) \le U$ for all $b, j, i$;
--   - for every $b$ and every point $z$ of nonzero weight under $(c_b).\mathrm{source}$, $\mathrm{length}(c_b)/4 \le z_{\mathrm{none}}$;
--   - $0 \le V$, $0 \le W$, $0 \le L$, $0 < \zeta \le 1$, $0 \le \varepsilon$, and $L \le \mathrm{length}(s_{b,j})$ for all $b, j$;
--   - $M$ is a positive natural number with $M / \bigl(\mathrm{length}(c_b) \prod_j \mathrm{length}(s_{b,j})\bigr) \le V$ for every $b$;
--   - $\mathcal{J}$ is a finite set of subsets of $I$, each of size at most $n + 1$;
--   - `positiveModerateSpectrumBlockCount n |𝒥| t` $\le |B|$, where `positiveModerateSpectrumBlockCount n j t` $= \max(\texttt{positiveModerateSpectrumExponent n j},\ \texttt{positiveModerateLengthExponent n} \cdot t) + 1$;
--   - $M^{|\mathcal{J}|} \le W L^t$;
--   - $\bigl(2\, \texttt{positiveModerateSpectrumConstant}\ n\ |\mathcal{J}|\ U\ V \cdot 2^{\texttt{positiveModerateSpectrumExponent}\ n\ |\mathcal{J}|} + W \bigl(2^{\texttt{positiveModerateLengthExponent}\ n} \cdot \texttt{positiveModerateLengthConstant}\ n\ U\bigr)^{t}\bigr)\, \zeta \le \varepsilon$.
--
--   All functions named in backticks are explicit constants or exponents defined by OpenAI.
--
--   **Conclusion.** For $k : \mathcal{J} \to \mathrm{Fin}\,M$ let
--   $$F(k) = \Bigl| \prod_{b \in B} \texttt{weightedAffineModerateGridCoefficient}\ c_b\ s_b\ u_b\ v_b\ 0\ M\ \mathcal{J}\ k \Bigr|,$$
--   where `weightedAffineModerateGridCoefficient c s u v shift M 𝒥 k` (defined by OpenAI) is the complex number $\mathbb{E}_{z \sim c.\mathrm{source}}\, \mathbb{E}_{x \sim \prod_j s_j.\mathrm{source}}\, e\bigl((\mathrm{shift} + z_{\mathrm{none}}) \cdot \Phi_k(x)\bigr)$, with $e(\theta) = e^{2\pi i \theta}$ and $\Phi_k(x)$ the Boolean block phase of the grid jet frequency of $k$ evaluated at the affine cube coordinates of the $x_j$ (`booleanBlockPhase`, `gridJetFrequency`, `affineCubeCoordinates`). Then
--   $$\sum_{k \notin \mathcal{C}} F(k) \le \varepsilon,$$
--   where $\mathcal{C}$ = `positiveModerateSpectrumCover 𝒥 M n U V L ζ` is a finite set of frequencies $k : \mathcal{J} \to \mathrm{Fin}\,M$ defined by OpenAI (a length-aware refinement of a polynomial grid cover), and the left side is `spectrumTail 𝒞 F`.
--
--   Lean: `OAI.Erdos3.weightedPositiveAffineModerate_uniform_spectrum_tail_s2`, which states OpenAI's `OAI.Erdos3.weightedPositiveAffineModerate_uniform_spectrum_tail` (in `lean/OAI/Combinatorics/Progressions/Fourier/FixedPrincipalCoefficientSpectrum.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B150` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/FixedPrincipalCoefficientSpectrum.lean (declaration OAI.Erdos3.weightedPositiveAffineModerate_uniform_spectrum_tail)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerate_uniform_spectrum_tail_s2 {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U V *
        2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ)
      (fun k => ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k‖) ≤ ε := by
  sorry

end Erdos3

end

end OAI
end
