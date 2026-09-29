-- Prove2me | Theorems.Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
-- name    : IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/6f3a34b2-34f6-5510-95b2-33b1fd48657d
-- title:
--   Algebraic Hartogs: height-one local membership implies integrality
-- statement:
--   Let $R$ be a noetherian integrally closed domain and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$ (so that the structure map $\mathrm{algebraMap}\colon R \to K$ is injective with $K$ obtained from $R$ by inverting the non-zero-divisors). Let $x \in K$, and assume that for every prime ideal $P$ of $R$ whose height equals $1$ there exist $a, s \in R$ with $s \notin P$ and $x \cdot \mathrm{algebraMap}(s) = \mathrm{algebraMap}(a)$ in $K$; that is, $x$ lies in the image of the localisation $R_P$ inside $K$, exhibited concretely as a fraction with denominator outside $P$. The conclusion is that $x$ belongs to the range of $\mathrm{algebraMap}\colon R \to K$, i.e. $x$ is the image of an element of $R$. This is the membership (division) form of the statement that such an $R$ is the intersection of its localisations at its height-one primes.
--
--   This is the algebraic Hartogs lemma, or Krull's theorem that a noetherian integrally closed domain equals the intersection of the localisations at its height-one primes, here in the form used by consumers: an element of the fraction field that is locally integral at every height-one prime is integral. It is invoked in the construction of local models on modular and elliptic curves, for instance in verifying that a function regular away from codimension two is globally regular, and in the derivation of the valuation-subring form of the same statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a) :
    x ∈ Set.range (algebraMap R K) := by sorry
