-- Prove2me | Theorems.Thm_GroupCohomology_RepImage_seq_shortExact
-- name    : GroupCohomology.RepImage.seq_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e54f8585-1868-5ab5-9f1e-5233e12b8ee6
-- title:
--   Image, target and cokernel form a short exact sequence
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and let $f : X \to Y$ be a morphism of $k$-linear representations of $G$. The short complex [`GroupCohomology.RepImage.seq f`](def/GroupCohomology_RepImage.html#L47) in $\mathrm{Rep}\,k\,G$ is the three-term complex whose first map is [`GroupCohomology.RepImage.ι f`](def/GroupCohomology_RepImage.html#L19), the inclusion of the image subrepresentation of $f$ into $Y$, and whose second map is [`GroupCohomology.RepCokernel.π f`](def/GroupCohomology_RepCokernel.html#L18), the quotient map from $Y$ onto the object [`GroupCohomology.RepCokernel.obj f`](def/GroupCohomology_RepCokernel.html#L13), namely $Y$ modulo the image of $f$; the composite vanishes because every element of the source of `ι f` satisfies the criterion [`GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff`](def/GroupCohomology_RepCokernel.html#L24) for being killed by $\pi$. The assertion is that this short complex is short exact in the sense of `ShortComplex.ShortExact`: `ι f` is a monomorphism, `π f` is an epimorphism, and the complex is exact at the middle term. Thus $0 \to \operatorname{im} f \to Y \to Y/\operatorname{im} f \to 0$ is short exact in $\mathrm{Rep}\,k\,G$, with no hypothesis on $f$.
--
--   This is the image–cokernel short exact sequence of representations, the standard input for the long exact sequence in group cohomology attached to an arbitrary morphism $f$ (in contrast to the companion sequence $0 \to X \to Y \to Y/f(X) \to 0$, which requires $f$ injective). It is used in the construction of the local restriction and Selmer-group pairing statements [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two) and [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepImage_seq_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

theorem GroupCohomology.RepImage.seq_shortExact {k G : Type} [CommRing k] [Group G] {X Y : Rep k G} (f : X ⟶ Y) :
    (GroupCohomology.RepImage.seq f).ShortExact := by sorry
