-- Prove2me | Theorems.Thm_OAI_Paper320_ballPredicate_sensitivityAt_zero_le
-- name    : OAI.Paper320.ballPredicate_sensitivityAt_zero_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:00.553387+00:00
-- url     : https://prove2.me/theorems/e9b032a1-651c-4c90-b030-0f92e8e561e1
-- title:
--   Rejected inputs of a union of well-separated Hamming balls have sensitivity at most $R+1$
-- statement:
--   Let $I$ and $C$ be finite sets and identify Boolean values with $\{0,1\}$. Write $d_H(x,y) = |\{ i \in I : x_i \ne y_i \}|$ for the Hamming distance on $\{0,1\}^I$, $x^{\{i\}}$ for the input $x$ with coordinate $i$ flipped, and $s(g, x) = |\{ i \in I : g(x^{\{i\}}) \ne g(x) \}|$ for the sensitivity of a Boolean function $g$ at $x$. Given centers $z_c \in \{0,1\}^I$ for $c \in C$ and a radius $R \in \mathbb{N}$, the ball predicate $\mathrm{Ball}_{z,R}$ accepts $x$ exactly when $d_H(x, z_c) \le R$ for some $c \in C$.
--
--   Assume that distinct centers are more than $2(R+1)$ apart:
--   $$
--   d_H(z_a, z_b) > 2(R+1) \qquad \text{for all } a \ne b \text{ in } C .
--   $$
--   Then every input $x \in \{0,1\}^I$ rejected by the ball predicate, $\mathrm{Ball}_{z,R}(x) = 0$, satisfies
--   $$
--   s(\mathrm{Ball}_{z,R}, x) \le R + 1 .
--   $$
--
--   The bound is independent of the number of centers and of the dimension $|I|$. Applied to the row indicators of the initial family of the construction separating block sensitivity from sensitivity (pairwise at distance $2(d+2)$, radii $d - q \le d$), it bounds the sensitivity of every initial predicate on its rejected inputs by $d+2$.
--
--   **Formalization Note** The centers form a function `centers : C → I → Bool`, the distance is Mathlib's `hammingDist`, and the predicate is `ballPredicate centers R`. If $C$ is empty the predicate is constantly false and its sensitivity is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/HammingBase.lean#L91-L113

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase

open OAI OAI.Paper320
open scoped Classical
variable {I C : Type} [Fintype I]

theorem OAI.Paper320.ballPredicate_sensitivityAt_zero_le [Fintype C]
    (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) (hx : ballPredicate centers R x = false) :
    sensitivityAt (ballPredicate centers R) x ≤ R + 1 := by sorry
