-- Prove2me | Theorems.Thm_GrandUnifiedTheories_beta_ker_card
-- name    : GrandUnifiedTheories.beta_ker_card
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:58:17.567248+00:00
-- url     : https://prove2.me/theorems/0761668c-2857-4171-8ac0-c479a3a639c9
-- title:
--   $\ker\beta$ has exactly three elements
-- statement:
--   The kernel of the Pati-Salam map is finite of order three:
--
--   $$\bigl|\ker\beta\bigr| \;=\; 3 .$$
--
--   Its elements are $(\alpha, I, \alpha^{-1}I)$ for $\alpha$ a cube root of unity, so $\ker\beta\cong\mathbb{Z}_3$ and the image of $\beta$ is a copy of $G_{\mathrm{SM}}/\mathbb{Z}_3$. This quantifies the difference between the two grand unified pictures at the level of groups: the $\mathrm{SU}(5)$ map $\varphi$ kills a $\mathbb{Z}_6$, the Pati-Salam map $\beta$ only a $\mathbb{Z}_3$, and the missing $\mathbb{Z}_2$ is recovered when the Pati-Salam group is traded for $\mathrm{Spin}(4)\times\mathrm{Spin}(6)$ and one descends to $\mathrm{SO}(4)\times\mathrm{SO}(6)$.
--
--   **Formalization note.** As with the previous milestone, the count follows directly from the formula for $\beta$ on p. 54 of the source but is not displayed there.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.3, p. 54 (order of the kernel of the displayed map β; computed directly from the formula, not displayed in the source)

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem beta_ker_card : Nat.card {x : GSM // betaMatrix x = (1, 1, 1)} = 3 := by sorry

end GrandUnifiedTheories
