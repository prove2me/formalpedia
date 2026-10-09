-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_original_global_physical_energy
-- name    : OAI.SevenEighths.InverseMoment.original_global_physical_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:51:26.807968+00:00
-- url     : https://prove2.me/theorems/bdefaf67-6a82-4f33-b799-7259f16fabf3
-- title:
--   Row-family energy split into dual zero, retained and tail parts
-- statement:
--   Let $p:\iota\to\mathcal O$ be a family of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda`, with residue characteristic $\ne2$ and `goodLambda`$^2\mid p_i-1$. Let `pool` be finite, $Q$ a finite set of exponent vectors supported in `pool`, `labels` finite nonzero ideals, $\beta$, $\Psi$, $m$, `mark`, $W$, $K>0$, $Y$, cutoff radii $R(b,C,I,D)\ge0$ (bounded by $Y$ on `firstOriginalOuter pool Q`), and $s:\mathrm{Fin}\,9\to\mathbb R$ positive. Then the `CanonicalRowCompletion.rowFamilyEnergy` (with $K$) of the `varyingReopenedRow` rows marked by `mark` and $W$ is at most
--   $$\|\Sigma_{\mathrm{dualZero}}\|+K\,\|\texttt{originalRetainedFamily}\cdots\|+\|\Sigma_{\mathrm{dualTail}}\|,$$
--   where $\Sigma_{\mathrm{dualZero}}$ and $\Sigma_{\mathrm{dualTail}}$ are `reopenedPhysicalSourceSum` of `canonicalCubeDualZero`, respectively `canonicalCubeDualTail` (with `rowMajorant`, $K$ and the cutoff `reopenedPhysicalCutoff p b I (R b C I)`).
--
--   Lean: `OAI.SevenEighths.InverseMoment.original_global_physical_energy` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstGlobalSourceEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B009

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_global_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (K Y : ℝ) (hK : 0<K)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    K*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant K Y R s‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
