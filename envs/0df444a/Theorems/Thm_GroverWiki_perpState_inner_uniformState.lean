-- Prove2me | Theorems.Thm_GroverWiki_perpState_inner_uniformState
-- name    : GroverWiki.perpState_inner_uniformState
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:39:19.646072+00:00
-- url     : https://prove2.me/theorems/235caa33-9318-47aa-ba81-6237df085dc4
-- title:
--   The initial ket is close to $|s'\rangle$: $\langle s'|s\rangle = \sqrt{(N-1)/N}$
-- statement:
--   Let $N \ge 2$, let $\omega \in \{0,\dots,N-1\}$, let $|s\rangle = \frac{1}{\sqrt N}\sum_x|x\rangle$ and $|s'\rangle = \frac{1}{\sqrt{N-1}}\sum_{x\ne\omega}|x\rangle$. Then
--
--   $$\langle s'|s\rangle = \sqrt{\frac{N-1}{N}} .$$
--
--   Equivalently, the angle $\theta/2$ between $|s\rangle$ and $|s'\rangle$ satisfies $\cos\frac\theta2 = \sqrt{(N-1)/N}$, i.e. $\sin\frac\theta2 = \frac{1}{\sqrt N}$: the initial state is close to the state orthogonal to $|\omega\rangle$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Geometric proof" (PDF p. 5)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- The initial ket is close to `|s'⟩`: `⟨s'|s⟩ = √((N-1)/N)`. -/
theorem perpState_inner_uniformState {N : ℕ} (hN : 2 ≤ N) (ω : Fin N) :
    star (perpState ω) ⬝ᵥ uniformState N = (Real.sqrt (((N : ℝ) - 1) / N) : ℂ) := by sorry

end GroverWiki
