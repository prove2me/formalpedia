-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_ringHom_padicInt_of_isFractionRing_rat
-- name    : IsDiscreteValuationRing.exists_ringHom_padicInt_of_isFractionRing_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/0c9ab7bf-d4ad-560f-887e-3ef1631bb9ea
-- title:
--   A DVR with fraction field ℚ and uniformiser p maps to ℤₚ
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, equipped with an algebra structure over $\mathbb{Q}$ making $\mathbb{Q}$ the field of fractions of $R$ in the sense of `IsFractionRing` (so `algebraMap R ℚ` is injective and identifies $\mathbb{Q}$ with the localisation of $R$ at its nonzero elements). Let $p$ be a prime natural number and assume that the image of $p$ in $R$ is irreducible. Then there exists a ring homomorphism $f \colon R \to \mathbb{Z}_p$ compatible with the inclusions into $\mathbb{Q}_p$: for every $r \in R$, the image of $f(r)$ under the coercion $\mathbb{Z}_p \to \mathbb{Q}_p$ equals the image of `algebraMap R ℚ r` under `algebraMap ℚ ℚ_[p]`. Equivalently, the composite $R \hookrightarrow \mathbb{Q} \to \mathbb{Q}_p$ has image contained in $\mathbb{Z}_p$ and thus factors through the ring of $p$-adic integers; the homomorphism $f$ produced is exactly this factorisation, and it is automatically injective since the stated compatibility identifies it with an injective composite.
--
--   This is the concrete form of Ostrowski's theorem for $\mathbb{Q}$ needed in practice: a discrete valuation ring with fraction field $\mathbb{Q}$ in which $p$ is irreducible is the local ring $\mathbb{Z}_{(p)}$, which embeds into the completion $\mathbb{Z}_p$. It is used by [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr) to transport an integral model over such a ring to one over $\mathbb{Z}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_ringHom_padicInt_of_isFractionRing_rat.lean

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsDiscreteValuationRing.exists_ringHom_padicInt_of_isFractionRing_rat
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    ∃ f : R →+* ℤ_[p], ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r) := by sorry
