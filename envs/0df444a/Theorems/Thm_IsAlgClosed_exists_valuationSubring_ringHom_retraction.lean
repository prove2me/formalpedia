-- Prove2me | Theorems.Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction
-- name    : IsAlgClosed.exists_valuationSubring_ringHom_retraction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/8eb8940c-0446-5c67-8ac4-31e70f3b8a15
-- title:
--   Existence of a K-rational place of K' over algebraically closed K
-- statement:
--   Let $K$ and $K'$ be fields, with $K$ algebraically closed, and let $K'$ be a $K$-algebra (so $\mathrm{algebraMap}\colon K \to K'$ is the structure map; since $K$ is a field and $K'$ a ring with $1 \neq 0$, this map is injective). The assertion is that there exist a valuation subring $A$ of $K'$, a proof $h_K$ that $\mathrm{algebraMap}\,c \in A$ for every $c \in K$, and a ring homomorphism $\sigma\colon A \to K$ such that two conditions hold: the kernel of $\sigma$ is exactly the maximal ideal of the local ring $A$, and $\sigma$ restricted along the inclusion of $K$ retracts the structure map, i.e. $\sigma(\mathrm{algebraMap}\,c) = c$ for all $c \in K$ (the element being taken with the membership witness $h_K\,c$). Thus $A$ is a valuation ring of $K'$ containing the image of $K$, and $\sigma$ induces an isomorphism of the residue field $A/\mathfrak{m}_A$ onto $K$ which is the identity on $K$; in particular $\sigma$ is surjective. Note that the membership witness $h_K$ is bound existentially, so it is part of the data produced.
--
--   This is Chevalley's place-extension theorem in the special case of the identity of an algebraically closed field $K$: every extension $K'/K$ admits a $K$-rational place, presented in valuation-ring form. It is used to produce a reduction map defined over the constant field in [`AlgebraicCurve.exists_constantReduction_of_constantFieldExtension`](thm.html#AlgebraicCurve.exists_constantReduction_of_constantFieldExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsAlgClosed.exists_valuationSubring_ringHom_retraction
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by sorry
