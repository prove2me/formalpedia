-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_eq_empty_or_eq_univ_of_forall_fst_mem_iff_snd_mem
-- name    : ModularCurve.SSLevelDatum.eq_empty_or_eq_univ_of_forall_fst_mem_iff_snd_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/dc0b9189-830b-56c3-a4c8-c1bbb9d61c15
-- title:
--   Connectedness of the s-isogeny graph of supersingular points of X₀(M)
-- statement:
--   Fix natural numbers $M, s, q'$ with $M, s$ nonzero, $q'$ prime, $s$ prime, $q' \ge 5$, $s \ne q'$, and neither $q'$ nor $s$ dividing $M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa =$ `IsLocalRing.ResidueField A` has decidable equality and characteristic $q'$. Let $X$ be an instance of the project's structure `SSLevelDatum q' κ M s`; it packages: the memberships of $j(q^M)$ and $j(q^s)$ in the level-$Ms$ modular function field $\kappa(j(q), j(q^{Ms}))$, integrality of the two level-raising maps `levelAlphaC` (the inclusion of $\kappa(j(q),j(q^M))$) and `levelBetaC` (induced by $q \mapsto q^s$ on $q$-expansions) and of all the Hecke degeneracy maps `heckeAlphaC`, `heckeBetaC`; the statements that restriction of places along these two maps carries supersingular places of level $Ms$ to supersingular places of level $M$ (a place being supersingular when it is rational, an affine geometric place, and its value at the geometric generator $j$ lies in the supersingular $j$-set for $q'$); an Atkin–Lehner automorphism interchanging the two generators in the prescribed way, under which the supersingular locus at level $Ms$ is stable; and a modular polynomial datum for $q'$ satisfying the Kronecker congruence. Write $X.fst$ and $X.snd$ for the resulting two degeneracy maps from the supersingular places of level $Ms$ to those of level $M$. Then for any subset $P$ of the supersingular places of level $M$ such that for every supersingular place $W$ of level $Ms$ one has $X.fst\,W \in P$ if and only if $X.snd\,W \in P$, either $P$ is empty or $P$ is everything.
--
--   This is the connectedness half of the two arithmetic inputs to Ribet's surjectivity theorem for the map $\mathbb{Z}[\Sigma(Ms)]_0 \to \mathbb{Z}[\Sigma(M)]_0^{\oplus 2}$: the supersingular points of $X_0(M)$ in characteristic $q'$ form the vertices, and those of $X_0(Ms)$ the edges, of the $s$-isogeny graph, and the assertion is that a vertex subset closed under passage between the two ends of every edge is trivial. It is used by [`CerednikDrinfeld.classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree`](thm.html#CerednikDrinfeld.classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree) and by [`ModularCurve.SSLevelDatum.exists_mem_characterLattice_degeneracyMatrix_mulVec_eq_pair`](thm.html#ModularCurve.SSLevelDatum.exists_mem_characterLattice_degeneracyMatrix_mulVec_eq_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_eq_empty_or_eq_univ_of_forall_fst_mem_iff_snd_mem.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.eq_empty_or_eq_univ_of_forall_fst_mem_iff_snd_mem
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    (P : Set ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)))
    (hP : ∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), X.fst W ∈ P ↔ X.snd W ∈ P) :
    P = ∅ ∨ P = Set.univ := by sorry
