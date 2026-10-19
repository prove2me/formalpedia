-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedForecastPolynomial_crt_decay_of_bad_product_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:53:33.293837+00:00
-- url     : https://prove2.me/theorems/71d48ec7-3243-42c6-b6f9-b360bd0f0271
-- title:
--   Character decay of the forecast polynomial under the CRT input law
-- statement:
--   Let $m,L\in\mathbb N$, $G,X$ finite types, $I,E\colon\mathrm{Fin}\,m\to$ Type families of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, and $B$ a family of finite types indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$. Let `inactive` be a predicate on `LayerSamplerAxis I n`; `noise` $\colon\mathrm{Option}($`LayerSamplerVariables G I n B`$)\times X\to\mathbb Z$; $r_j\colon$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)` $\to E_j\to\mathbb Z$; `projection` $j\colon$ `AllocatedDegreeActiveAxis inactive j` $\to$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)` $\to\mathbb Z$; and embeddings `spatial` $\colon\mathrm{Fin}\,L\hookrightarrow G$, `kernel` $j\colon\mathrm{Fin}\,L\times\mathrm{Fin}(j+1)\hookrightarrow G$, `block` $j\ a\colon\mathrm{Fin}\,L\hookrightarrow B\langle j,a\rangle$. Assume $m>0$. Let $\mathrm{Pr}$ be a finite set of primes, $A,e\colon\mathbb N\to\mathbb N$, $C\ge0$ real and $R_{\mathrm{bad}}\in\mathbb N$ with $\prod_{p\in\mathrm{Pr}}p^{\beta(p)}\le R_{\mathrm{bad}}$, where $\beta=$ `allocatedCongruenceBadDepth inactive noise r projection spatial kernel block Pr A C` (a function $\mathbb N\to\mathbb N$, the `largestTestedBadDepth` of the predicate `allocatedCongruenceRankBad`). Write $Q=\prod_{p\in\mathrm{Pr}}p^{A(p)}$. Let `base` $\colon X\to\mathbb Z$; for each $p\in\mathrm{Pr}$ let $\mathrm{origin}_p\colon$ `LayerSamplerLongVariables inactive G B` $\to\mathbb Z/p^{A(p)}$; let `raw` $\colon$ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\times\mathrm{Option}\,\mathrm{Empty}\to\mathbb Z$; and let $\chi$ be an additive character on functions from $\Sigma_j$ `AllocatedCongruenceRankOutput X E inactive j` to $\mathbb Z/Q$. Let $\lambda=$ `crtPolynomialInputLaw` (with primes $p$, exponents $A(p)$, $e(p)$, the pairwise coprimality of the $p^{A(p)}$, and the origins), a `FiniteProbabilityWeights` on functions from `LayerSamplerLongVariables inactive G B` to $\mathbb Z/Q$, and let $Y(t)_o$ be the reduction mod $Q$ of `integerLongPolynomialOutput (allocatedForecastPolynomial inactive base noise r projection) raw Q t o`, i.e. of the integer polynomial `allocatedForecastPolynomial … o` evaluated at the representatives in $[0,Q)$ of $t$ and at `raw`. Then
--   $$\Big|\sum_t\lambda(t)\,\chi(Y(t))\Big|\le\Big(R_{\mathrm{bad}}\prod_{p\in\mathrm{Pr}}p^{e(p)}\Big)^{\kappa\cdot\gamma}\cdot\mathrm{ord}(\chi)^{-\kappa},$$
--   the left side being `finiteImageCharacteristic λ Y χ`, where $\kappa=$ `modularRankDecayExponent m C` $=C/(2^m m!)/2^m$, $\gamma=$ `modularRankChargeFactor m` $=4m\cdot2^m m!$, and $\mathrm{ord}(\chi)$ is the order of $\chi$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedForecastShortRawDependence.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B219` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedForecastShortRawDependence.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_crt_decay_of_bad_product)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B219

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

local instance forecastModulusNeZero_r1f3108_1 (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

theorem allocatedForecastPolynomial_crt_decay_of_bad_product_s2
    (hm : 0 < m) (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (C : ℝ) (hC : 0 ≤ C) (Rbad : ℕ)
    (hbad : (∏ p : Pr, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block Pr A C p.val) ≤ Rbad)
    (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : Pr, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq Pr := Classical.decEq _
    ‖finiteImageCharacteristic
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val)
        (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective) origin)
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val) t j : ZMod (∏ p : Pr, p.val ^ A p.val))) χ‖ ≤
      ((Rbad * ∏ p : Pr, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
