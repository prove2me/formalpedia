-- Prove2me | Theorems.Thm_ModularCurve_periodHomPair_eichlerShimura
-- name    : ModularCurve.periodHomPair_eichlerShimura
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/5c1bbafb-db42-576b-92d4-6bb5766d7177
-- title:
--   Eichler–Shimura: period pair map injective with parabolic image
-- statement:
--   Let $N$ be a natural number, assumed nonzero. The statement concerns the $\mathbb{C}$-linear map [`ModularCurve.periodHomPair N`](def/ModularCurve_PeriodHomPair.html#L135) from the square $\mathrm{CuspForm}(\Gamma_0(N),2) \times \mathrm{CuspForm}(\Gamma_0(N),2)$ of the space of weight-$2$ cusp forms for $\Gamma_0(N)$ to the space of additive homomorphisms from $\Gamma_0(N)$, viewed additively, to $\mathbb{C}$. That map is defined by a case distinction on the predicate `ExistsPeriodMapLinear N`, namely that the period assignment $f \mapsto$ `periodMap N f` is realised by some $\mathbb{C}$-linear map $\mathrm{pml}$: if such a map exists, `periodHomPair N` is the coproduct of $(\mathrm{id} + \iota) \circ \mathrm{pml}$ and $(\mathrm{id} - \iota) \circ \mathrm{pml}$, where $\iota$ is `charInvolution`, precomposition of a homomorphism with the conjugation automorphism `jConjGamma0 N` of $\Gamma_0(N)$; otherwise it is the zero map. The assertion is the conjunction of two facts: `periodHomPair N` is injective, and its range is exactly the submodule `parabolicHoms` of those homomorphisms $\varphi$ that vanish on every $\gamma \in \Gamma_0(N)$ whose matrix satisfies $\mathrm{tr}(\gamma)^2 = 4$.
--
--   This is the Eichler–Shimura isomorphism in unbundled form: the two copies of weight-$2$ cusp forms (holomorphic and antiholomorphic periods, separated by the eigenspaces of the conjugation involution) parametrise exactly the parabolic homomorphisms $\Gamma_0(N) \to \mathbb{C}$. It is used in the construction of bases and of Hecke actions on the parabolic cohomology carrier, for instance by [`CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank`](thm.html#CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank), [`CohCarrier.exists_eichlerShimura_H1_top`](thm.html#CohCarrier.exists_eichlerShimura_H1_top) and [`CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms`](thm.html#CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodHomPair_eichlerShimura.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.periodHomPair_eichlerShimura (N : ℕ) [NeZero N] :
    Function.Injective (ModularCurve.periodHomPair N)
      ∧ LinearMap.range (ModularCurve.periodHomPair N)
          = ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ := by sorry
