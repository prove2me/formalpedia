-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_IntegralFamily_main_of_oddValues
-- name    : OAI.DeligneDrinfeld.IntegralFamily.main_of_oddValues
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:45:30.974987+00:00
-- url     : https://prove2.me/theorems/fcf524c6-d28c-48a1-8ab4-afcb8071184e
-- title:
--   Section 8 (OpenAI, Deligne–Drinfeld) — the dimension squeeze: an Ihara-closed subspace with odd depth-one values gives the Deligne–Drinfeld isomorphism
-- statement:
--   Let $V$ be a family of values (`IntegralFamily.Values`): a $\mathbb Q$-subspace of $L = \mathrm{Lie}_{\mathbb Q}\langle x, y\rangle$ contained in the solution space $W$ and closed under the Ihara bracket. Suppose $V$ has odd values (`IntegralFamily.OddValues V`): for every $k \ge 0$ there is $p \in W_{2k+3}$ lying in the weight-$(2k+3)$ part of $V$ whose image in the free associative algebra $\mathbb Q\langle x, y\rangle$ has a nonzero coefficient on the word $x^{2k+2}y$. Then `MainStatement` holds: the published statement of the Deligne–Drinfeld conjecture, that there is a graded linear isomorphism $e$ from the free Lie algebra on generators of weights $3, 5, 7, \dots$ onto $W$ that carries the Lie bracket to the Ihara bracket and induces a continuous isomorphism of the weight completions compatible with the brackets.
--
--   $$V \subseteq W \text{ Ihara-closed},\ \ \forall k\ \exists\, p \in V \cap W_{2k+3}:\ \operatorname{coeff}_{x^{2k+2}y}(p) \neq 0 \ \Longrightarrow\ \texttt{MainStatement}.$$
--
--   `MainStatement`, $W$, $W_n$, $L$ and `ihara` are the published definitions of the bundle `DeligneDrinfeld`; `Values`, `OddValues`, the weight pieces and the associative embedding are OpenAI's, from the bundle `Def_DeligneDrinfeldInternals`.
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), §8, p. 39: “If $n$ is even, this already attains the upper bound (8.1). If $n \ge 3$ is odd, Proposition 7.3 gives $\tau_n \in V_n$ with a nonzero coefficient of $x^{n-1}y$. Every old Hall-word value of weight $n$ is decomposable and has zero depth-one component by Lemma 8.1. Hence $\tau_n$ is independent of them. In both cases, $\dim_{\mathbb Q} V_n = \dim_{\mathbb Q} W_n = d_n$.” This is OpenAI's Lean theorem `OAI.DeligneDrinfeld.IntegralFamily.main_of_oddValues` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0): §8's inductive choice of integral generators and the dimension squeeze against the upper bound of §5, with the conclusion of Theorem 1.1. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Section 8, pp. 38-40 (the dimension squeeze); Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldInternals

namespace OAI.DeligneDrinfeld.IntegralFamily

theorem main_of_oddValues (V : OAI.DeligneDrinfeld.IntegralFamily.Values)
    (h : OAI.DeligneDrinfeld.IntegralFamily.OddValues V) : OAI.DeligneDrinfeld.MainStatement := by
  sorry

end OAI.DeligneDrinfeld.IntegralFamily
