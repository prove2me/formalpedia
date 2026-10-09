-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_canonical_first_physical_split
-- name    : OAI.SevenEighths.InverseMoment.canonical_first_physical_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:33:42.128714+00:00
-- url     : https://prove2.me/theorems/dad766ad-0993-4669-88a0-9f69970db5cc
-- title:
--   Canonical cube before Poisson splits into zero mode, physical modes and tail
-- statement:
--   Let $p:\iota\to\mathcal O$ (Eisenstein integers) be a family of nonzero elements generating maximal ideals that are pairwise coprime, injective as ideals, avoid `goodLambda` (with `goodLambda`$^2\mid p_i-1$) and have residue characteristic $\ne2$. For a finite `pool`, `b : CubeCoordinates ι` with `b.Admissible`, a finite $C$ disjoint from `b.support`, multiplicative maps $\Psi_1,\Psi_2:\mathcal O\to\mathbb C$, $m_1,m_2\in\mathcal O$, a nonzero ideal $f$, $H_1,H_2:\mathrm{Finset}\,\iota\to\mathbb C$, $W_1,W_2:\mathbb R\to\mathbb C$, a Schwartz $\Phi$, $K>0$ and radii $R(D)\ge0$: writing $f_{\mathrm{gen}}$ = `idealGenerator f`, $H_i'(U)=H_i(U)W_i(\texttt{primeProductNorm}\,p\,U)$ and $T(D)$ the `childFrequencyBall` of `firstPhysicalMultiplier` of radius $R(D)$, the quantity `canonicalCubeBeforePoisson` equals `canonicalCubeDualZero` plus `canonicalCubeOuter` times
--   $$\sum_{D\subseteq C\cup\texttt{cubePrincipalSupport}}\mu\Big(\prod_{i\in D}(p_i)\Big)\sum_{h\in T(D)\setminus\{0\}}\texttt{firstCubePhysicalMode}(\dots,\texttt{primeSubsetGenerator}\,D,\,h)$$
--   plus `canonicalCubeDualTail` (all with these arguments; $\mu$ is the Möbius function on ideals).
--
--   Lean: `OAI.SevenEighths.InverseMoment.canonical_first_physical_split` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstRetainedPhysical.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B007

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_first_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (f : Ideal O) (hf : f≠0) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (R : Finset ι→ℝ)
    (hR : ∀ D,0≤R D) :
    let fgen := ConcretePrimeRowBridge.idealGenerator f
    let H₁' := fun U=>H₁ U*W₁ (primeProductNorm p U)
    let H₂' := fun U=>H₂ U*W₂ (primeProductNorm p U)
    let T := fun D=>childFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D)
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K =
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K +
      (canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ fgen *
        ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
          ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁ H₂
            W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h) +
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K T := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
