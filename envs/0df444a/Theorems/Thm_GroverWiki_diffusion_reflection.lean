-- Prove2me | Theorems.Thm_GroverWiki_diffusion_reflection
-- name    : GroverWiki.diffusion_reflection
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:37:33.219338+00:00
-- url     : https://prove2.me/theorems/97f99844-14b8-4a03-9294-49864a19b7de
-- title:
--   $U_s = 2|s\rangle\langle s| - I$ is the reflection through $|s\rangle$
-- statement:
--   Let $|s\rangle = \frac{1}{\sqrt N}\sum_{x=0}^{N-1}|x\rangle$ and $U_s = 2|s\rangle\langle s| - I$. Then $U_s$ is the reflection through $|s\rangle$:
--
--   1. $U_s|s\rangle = |s\rangle$;
--   2. $U_s|v\rangle = -|v\rangle$ for every $|v\rangle \in \mathbb C^N$ with $\langle s|v\rangle = 0$.
--
--   Together with the oracle's reflection property, this is what keeps the state of Grover's algorithm in a two-dimensional plane.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Geometric proof" (PDF p. 4)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- `U_s = 2|s⟩⟨s| - I` is the reflection through `|s⟩`: it fixes `|s⟩` and negates every
vector orthogonal to `|s⟩`. -/
theorem diffusion_reflection (N : ℕ) :
    diffusion N *ᵥ uniformState N = uniformState N ∧
      ∀ v : Fin N → ℂ, star (uniformState N) ⬝ᵥ v = 0 → diffusion N *ᵥ v = -v := by sorry

end GroverWiki
