-- Prove2me | Theorems.Thm_MPSTAsync_Progress_theorem_5_19_3
-- name    : MPSTAsync.Progress.theorem_5_19_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:18:46.689986+00:00
-- url     : https://prove2.me/theorems/f52ad577-6e86-40e1-8338-b7cf2cafbf11
-- title:
--   Theorem 5.19(3) — closed runtime typing is preserved by one reduction
-- statement:
--   Let $\Gamma$ be a well-formed shared-name environment. If a process $P$ has runtime typing $\Gamma\vdash P\triangleright_{\varnothing}\varnothing$ and takes one reduction step to $P'$, then $P'$ has the same empty queue and session typing:
--
--   $$\Gamma\vdash P\triangleright_{\varnothing}\varnothing\ \land\ P\longrightarrow P'\quad\Longrightarrow\quad\Gamma\vdash P'\triangleright_{\varnothing}\varnothing.$$
--
--   This is the closed-program preservation clause used in progress.
--
--   **Formalization Note** Well-formedness of $\Gamma$ records the paper's standing convention that shared-name sorts contain coherent global types.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, p. 34, Theorem 5.19 (3), https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Activity

set_option autoImplicit false

namespace MPSTAsync.Progress

theorem theorem_5_19_3 (Γ : Env) (hΓ : Γ.WellFormed) (P P' : Proc)
    (hP : RTyped true Γ P [] []) (hred : Reduces P P') :
    RTyped true Γ P' [] [] := by sorry

end MPSTAsync.Progress
