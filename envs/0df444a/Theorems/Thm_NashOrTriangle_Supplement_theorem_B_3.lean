-- Prove2me | Theorems.Thm_NashOrTriangle_Supplement_theorem_B_3
-- name    : NashOrTriangle.Supplement.theorem_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:52:27.185274+00:00
-- url     : https://prove2.me/theorems/a9868be1-5709-402d-8d09-7f471b351b19
-- title:
--   Theorem B.3 — existence of a value is $\Pi^0_2$-complete for Turing-machine games
-- statement:
--   **Theorem B.3.** Consider binary games on $\mathbb N\times\mathbb N$ given by a total utility Turing machine and best-response Turing machines that take a rational accuracy parameter $\varepsilon>0$ and return an $\varepsilon$-best response. For such games, the existence of a value,
--   $$\sup_p L(p)=\inf_q U(q),$$
--   with $p$, $q$ ranging over countably additive mixed strategies, is $\Pi^0_2$-complete: it is $\Pi^0_2$ on valid instances, and every $\Pi^0_2$ set reduces to it by a computable map producing valid instances.
--
--   The theorem is the recursion-theoretic counterpart of the fact that, in the oracle model, whether the game has a value cannot be inferred even after infinitely many calls.
--
--   **Formalization Note** Programs are Mathlib partial recursive codes; no time bound is imposed (`ValidApprox`).
--
--   Differences from the source:
--   - encoding: binary games given by valid total utility and BR Turing machines (BR machines take a rational accuracy parameter and meet it) → instance codes under ValidApprox: total binary utility program, BR programs returning ε-best responses on every finite rational mixture and rational ε > 0; reason: the model of the first paragraph of Appendix B
--   - encoding: the existence of a value is Π⁰₂-complete → PromisePi02Complete for HasValuePMF (sup over PMF ℕ of L = inf over PMF ℕ of U); reason: §1.1 definition of the value; completeness of a promise problem
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem B.3, p.23 (PDF p.24); model: Appendix B, first paragraph, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_NashOrTriangle_Supplement_PMFGame
import Definitions.Def_NashOrTriangle_Supplement_TMGame
import Definitions.Def_NashOrTriangle_Supplement_Arithmetical

namespace NashOrTriangle.Supplement

/-- **Theorem B.3** (the value in the Turing-machine model). For binary games given by valid
total utility and BR Turing machines, the existence of a value is `Π⁰₂`-complete.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem B.3, printed p. 23 (PDF p. 24);
the model is the first paragraph of Appendix B, printed p. 22 (PDF p. 23): "a BR Turing machine
takes a rational accuracy parameter and is promised to meet it".

**Formalization Note** Instances are codes `I` of a triple of programs (`tmInstance`) under the
promise `ValidApprox` (total binary utility program; BR programs that, on a finite rational
mixture and a rational `ε > 0`, return an `ε`-best response; no time bound). The game has a value
when `sup_p L(p) = inf_q U(q)` over countably additive mixed strategies (`PMF ℕ`, §1.1).
`Π⁰₂`-completeness is membership and hardness of the promise problem (`PromisePi02Complete`). -/
theorem theorem_B_3 :
    PromisePi02Complete ValidApprox (fun I => HasValuePMF (tmPayoff I)) := by sorry

end NashOrTriangle.Supplement
