-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
-- name    : NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/71bd39db-1e95-53d9-871e-c8bf3eacbeaf
-- title:
--   Completion at a finite place as a finite layer of ℚ̄_q
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an extension of $E$ that is Galois, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Write $\mathrm{decomp}\ E\ K\ w$ for the decomposition subgroup of $K \simeq_{\mathrm{alg}[E]} K$ attached to the valuation subring of the $w$-adic valuation of $K$. The assertion is that there exist a prime number $q$, an intermediate field $L'$ of the algebraic closure `PadicAlgCl q` over $\mathbb{Q}_q$ which is finite-dimensional over $\mathbb{Q}_q$, an action of the group $\mathrm{decomp}\ E\ K\ w$ on $L'$ by ring automorphisms that is faithful, a compatible multiplicative action of that group on the unit group $(L')^{\times}$, and a ring isomorphism $\Phi \colon K_w \to L'$ from the $w$-adic completion of $K$ onto $L'$, such that: every group element fixes each element of the image of $\mathbb{Q}_q$ in $L'$ under the structure map; the action on $(L')^{\times}$ is induced by the action on $L'$, i.e. $(g \cdot u)$ and $g \cdot u$ agree as elements of $L'$; $\Phi$ is equivariant, $\Phi(g \cdot x) = g \cdot \Phi(x)$ for the given action of the decomposition group on $K_w$; and the image of $q$ in $\mathcal{O}_K$ lies in the prime ideal of $w$, so that $q$ is the residue characteristic of $w$.
--
--   This identifies the completion $K_w$, together with the action of the decomposition group of $w$ in $\mathrm{Gal}(K/E)$, with a finite extension of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying an action of the same group by $\mathbb{Q}_q$-algebra automorphisms, $q$ being the residue characteristic of $w$. It is the transfer point between the local cohomological machinery formulated for finite layers of $\overline{\mathbb{Q}}_q$ with an abstract finite group and the global statements phrased over completions; it is used by the Herbrand-quotient and local fundamental class computations that invoke decomposition groups at finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory groupCohomology ExtCitation.LocalLevel IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
      (_ : MulSemiringAction (decomp E K w) L') (_ : FaithfulSMul (decomp E K w) L')
      (_ : MulDistribMulAction (decomp E K w) (↥L')ˣ)
      (Φ : w.adicCompletion K ≃+* L'),
      (∀ (g : decomp E K w) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) ∧
      (∀ (g : decomp E K w) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L')) ∧
      (∀ (g : decomp E K w) (x : w.adicCompletion K), Φ (g • x) = g • Φ x) ∧
      ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by sorry
