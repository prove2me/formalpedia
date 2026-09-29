-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_brown_free_lie_subalgebra
-- name    : GrothendieckTeichmuller.brown_free_lie_subalgebra
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T21:56:27.290509+00:00
-- url     : https://prove2.me/theorems/f3b4a391-7e64-4ad9-8954-7e085b00000e
-- title:
--   F. Brown — the $\sigma_{2p+3}$ generate a free Lie subalgebra of $\mathfrak{grt}_1$
-- statement:
--   There exists a family $(\sigma_p)_{p \ge 0}$ of elements of $\mathfrak{grt}_1$, with $\sigma_p$ homogeneous of degree $2p+3$, generating a **free** Lie subalgebra for the Ihara bracket.
--
--   Freeness is expressed on the derivation side. Writing $D_f$ for the Ihara derivation attached to $f$ and $\mathrm{Der}$ for the Lie algebra of derivations of $\mathbb F(x,y)$ under the commutator, the Lie algebra morphism
--
--   $$\mathbb F(\mathbb N) \longrightarrow \mathrm{Der}, \qquad p \longmapsto D_{\sigma_p},$$
--
--   from the free Lie algebra on countably many generators is **injective**. Since $[D_f,D_g] = D_{\{f,g\}}$ and $f \mapsto D_f$ is injective on $\mathfrak{grt}_1$, this says precisely that the $\sigma_p$ satisfy no relations beyond those forced by the Lie axioms for the Ihara bracket.
--
--   This is the half of the Deligne-Drinfeld-Ihara conjecture established by F. Brown's theorem on motivic multiple zeta values; the remaining half, that these elements exhaust $\mathfrak{grt}_1$, is the mission's goal.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 7.4, p. 58, Theorem 7.1 and Corollary 7.2 (F. Brown); see also F. Brown, Mixed Tate motives over Z, Ann. of Math. 175 (2012), 949-976, doi:10.4007/annals.2012.175.2.10

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem brown_free_lie_subalgebra :
    ∃ sigma : ℕ → Lxy,
      (∀ p, sigma p ∈ grt1 ∧ IsHomogeneousOfDegree (2 * p + 3) (sigma p)) ∧
      Function.Injective
        ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) := by sorry

end GrothendieckTeichmuller
