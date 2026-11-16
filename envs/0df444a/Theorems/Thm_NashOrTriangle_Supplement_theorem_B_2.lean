-- Prove2me | Theorems.Thm_NashOrTriangle_Supplement_theorem_B_2
-- name    : NashOrTriangle.Supplement.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:51:53.231936+00:00
-- url     : https://prove2.me/theorems/8c861aba-0586-4b5a-9b08-c678d4cc2311
-- title:
--   Theorem B.2 — existence of a $1/k$-Nash equilibrium is undecidable for polynomial-time Turing-machine games
-- statement:
--   **Theorem B.2.** Fix $k\ge3$. Among binary games on $\mathbb N\times\mathbb N$ given by a total polynomial-time utility Turing machine and exact polynomial-time best-response Turing machines on unary strategy descriptions, the existence of a $1/k$-Nash equilibrium is undecidable: no computable function decides, for every such instance, whether the game has a pair of mixed strategies $(p,q)$ with
--   $$U(q)-M(p,q)\le\frac1k,\qquad M(p,q)-L(p)\le\frac1k .$$
--
--   Mixed strategies are countably additive distributions on $\mathbb N$, as in the paper's definitions. The theorem is the recursion-theoretic counterpart of the impossibility of finding approximate equilibria in the oracle model.
--
--   **Formalization Note** Instances and the validity promise are those of Theorem B.1 (`ValidExactPoly`).
--
--   Differences from the source:
--   - encoding: binary games with polynomial-time utility and exact BR Turing machines on unary strategy descriptions → instance codes under ValidExactPoly; reason: as in Theorem B.1
--   - encoding: the existence of a 1/k-Nash equilibrium is undecidable → PromiseUndecidable: no computable d : ℕ → Bool agrees on every valid instance with the existence of PMF ℕ strategies (p, q) satisfying IsNashPMF at 1/k; reason: §1.1: mixed strategies are countably additive; undecidability of a promise problem
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem B.2, p.22 (PDF p.23); model: Appendix B, first paragraph, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_NashOrTriangle_Supplement_PMFGame
import Definitions.Def_NashOrTriangle_Supplement_TMGame
import Definitions.Def_NashOrTriangle_Supplement_Arithmetical

namespace NashOrTriangle.Supplement

/-- **Theorem B.2** (Nash equilibria in the Turing-machine model). For any fixed `k ≥ 3`, the
existence of a `1/k`-Nash equilibrium is undecidable, even for binary games with polynomial-time
utility and exact BR Turing machines on unary strategy descriptions.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem B.2, printed p. 22 (PDF p. 23);
the model is the first paragraph of Appendix B, same page.

**Formalization Note** Instances are codes `I` of a triple of programs (`tmInstance`) under the
promise `ValidExactPoly` (total binary utility program, exact BR programs, all polynomial time on
unary strategies). A `1/k`-Nash equilibrium is a pair of countably additive mixed strategies
(`PMF ℕ`, §1.1) with `U(q) − M(p, q) ≤ 1/k` and `M(p, q) − L(p) ≤ 1/k`. Undecidable: no computable
function agrees with the property on every valid instance (`PromiseUndecidable`). -/
theorem theorem_B_2 (k : ℕ) (hk : 3 ≤ k) :
    PromiseUndecidable ValidExactPoly
      (fun I => ∃ (p q : PMF ℕ), IsNashPMF (tmPayoff I) (1 / (k : ℝ)) p q) := by sorry

end NashOrTriangle.Supplement
