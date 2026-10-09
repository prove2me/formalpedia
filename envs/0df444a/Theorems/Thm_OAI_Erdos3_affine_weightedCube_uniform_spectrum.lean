-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_weightedCube_uniform_spectrum
-- name    : OAI.Erdos3.affine_weightedCube_uniform_spectrum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T13:28:13.382151+00:00
-- url     : https://prove2.me/theorems/a7057b96-53e8-456c-a307-5a6f8d01965c
-- title:
--   Uniform spectrum bounds for products of affine weighted-cube grid coefficients
-- statement:
--   Let $B$ and $I$ be finite types ($I$ with decidable equality) and $n\in\mathbb N$. For each $b\in B$ and $j\in\mathrm{Fin}(n+1)$ let $s_{b,j}$ be a `NormalizedScalarCubeSource I` (a structure bundling a length $\ell>0$, a modulus bound, moduli $m_i>0$ and residues for $i\in\mathrm{Option}\,I$, and a bounded Lipschitz weight, normalized so that it determines a probability law `source` on `IntegerScalarCubeBox I ℓ`), $u_{b,j}\colon\mathrm{Option}\,I\to\mathbb R$ and $v_{b,j}\colon\mathrm{Option}\,I\to\mathbb N$. Let $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz, and reals $U,V,W,L,\varepsilon$ with $1\le U$, $0\le V$, $0\le W$, $0\le L$, $0<\varepsilon$. Assume `ScalarCubePrimitiveBudget (s b j) A U` for all $b,j$ (a predicate bounding $|I|+1$, the modulus bound, the weight bound, the weight's Lipschitz constant and two boundary constants of the scalar cube by $U$); $L\le\ell(s_{b,j})$; $v_{b,j}(i)>0$ and $v_{b,j}(i)\,m_i(s_{b,j})\le U$ for all $b,j,i$. Let $M,t\in\mathbb N$ with $M>0$, and let $J$ be a finite family of finite subsets of $I$ each of size at most $n+1$, with `uniformSpectrumBlockCount n |J| t` $\le|B|$, $M^{|J|}\le WL^t$, and $M/\prod_j\ell(s_{b,j})\le V$ for every $b$. Put $\zeta=$ `uniformBlockRetainedBias n |J| t U V W ε` and $S=$ `uniformBlockSpectrumCover J M n U V L ζ` (a finite set of frequencies $J\to\mathrm{Fin}\,M$). Writing $c(k)=\prod_{b\in B}$ `affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k` for $k\colon J\to\mathrm{Fin}\,M$, the conclusion is: $\sum_{k\notin S}|c(k)|\le\varepsilon$ (`spectrumTail`), and $\sum_k|c(k)|\le$ `uniformSpectrumAbsoluteCap n |J| t U V W`. Here `affineWeightedCubeGridCoefficient s u v M J k` is the complex mean, under the product of the laws `(s j).source`, of the unit-circle character evaluated at the real phase `booleanBlockPhase` of the frequencies $S\mapsto k_S/M$ ($S\in J$, and $0$ off $J$) against the affine coordinates $i\mapsto u_j(i)+v_j(i)\,z_j(i)$ of the sample $z$; `uniformSpectrumBlockCount`, `uniformBlockRetainedBias` and `uniformSpectrumAbsoluteCap` are OpenAI's explicit numerical parameters (a natural number and two reals).
--
--   Lean: `OAI.Erdos3.affine_weightedCube_uniform_spectrum` in `lean/OAI/Combinatorics/Progressions/Fourier/AffineUniformSpectrum.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B088` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/AffineUniformSpectrum.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_uniform_spectrum {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    spectrumTail S (fun k => ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤ ε ∧
      (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card t U V W := by
  sorry

end Erdos3
end
end OAI
