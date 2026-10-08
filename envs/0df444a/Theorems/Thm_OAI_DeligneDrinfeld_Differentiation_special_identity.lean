-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_Differentiation_special_identity
-- name    : OAI.DeligneDrinfeld.Differentiation.special_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:42:56.809994+00:00
-- url     : https://prove2.me/theorems/8141036e-07a4-41b9-9cda-a083859b2258
-- title:
--   Lemma 2.4 (OpenAI, Deligne–Drinfeld) — the special identity [a, ψ(b,a)] + [c, ψ(b,c)] = 0 with c = −a − b
-- statement:
--   Let $\psi \in W_n$ with $n > 2$, that is, $\psi$ is a solution of the three defining equations of $W$ (antisymmetry, the three-term relation and the pentagon in $\mathfrak t_4$) and is homogeneous of weight $n$ in the free Lie algebra $L = \mathrm{Lie}_{\mathbb Q}\langle x, y\rangle$. Then for every Lie algebra $M$ over $\mathbb Q$ (in `Type`) and all $a, b \in M$,
--
--   $$[a,\ \psi(b, a)] + [-a-b,\ \psi(b, -a-b)] = 0,$$
--
--   where $\psi(u, v)$ is the image of $\psi$ under the Lie algebra homomorphism $L \to M$ sending $x \mapsto u$, $y \mapsto v$ (`eval u v`). $W$, $L_n$ and `eval` are the published definitions of the bundle `DeligneDrinfeld`.
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), p. 6: “Lemma 2.4 (The special identity). Let $\psi \in W_n$, where $n > 2$. In the free Lie algebra on $a, b$, with $c = -a - b$, one has $[a, \psi(b, a)] + [c, \psi(b, c)] = 0$. (2.4) In addition, for an extra free letter $T$, $\partial_2 \psi(a, -a)T = 0$, (2.5) where $\partial_2$ means the coefficient of a central parameter $t$ in $\psi(a, -a + tT)$.”
--
--   This is OpenAI's Lean theorem `OAI.DeligneDrinfeld.Differentiation.special_identity` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), which states identity (2.4) in every rational Lie algebra rather than only in the free one on $a, b$ (the two are equivalent, by the universal property). Identity (2.5) is not part of this statement. It is published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, p. 6, Lemma 2.4, identity (2.4); Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeld

namespace OAI.DeligneDrinfeld.Differentiation

theorem special_identity {M : Type} [LieRing M] [LieAlgebra ℚ M] {n : ℕ}
    {p : OAI.DeligneDrinfeld.L} (hp : p ∈ OAI.DeligneDrinfeld.W) (hpn : p ∈ OAI.DeligneDrinfeld.Ln n) (hn : 2 < n)
    (a b : M) : ⁅a, (OAI.DeligneDrinfeld.eval b a) p⁆ + ⁅-a - b, (OAI.DeligneDrinfeld.eval b (-a - b)) p⁆ = 0 := by
  sorry

end OAI.DeligneDrinfeld.Differentiation
