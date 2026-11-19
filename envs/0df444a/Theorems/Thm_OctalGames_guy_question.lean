-- Prove2me | Theorems.Thm_OctalGames_guy_question
-- name    : OctalGames.guy_question
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:02:27.963039+00:00
-- url     : https://prove2.me/theorems/f3dc76a3-aa74-4fad-b9df-3aaf01021eb5
-- title:
--   Is every finite octal game eventually periodic?
-- statement:
--   Let $\Gamma = d_0.d_1d_2\cdots d_k$ be any octal game of finite length, and let $\mathcal G_\Gamma(n)$ be the nim-value of a $\Gamma$-heap of $n$ tokens (see the definition `OctalGames_Code`). Then the nim-sequence of $\Gamma$ is eventually periodic: there exist $n_0\ge 0$ and $p\ge 1$ such that
--
--   $$
--   \mathcal G_\Gamma(n+p)=\mathcal G_\Gamma(n)\qquad\text{for all } n\ge n_0 .
--   $$
--
--   This is the question "Is every finite octal game eventually periodic?" asked in *Winning Ways* and recorded by Siegel as unresolved. Many octal games are known to be periodic: by the Octal Periodicity Theorem, a finite computation suffices once periodicity has set in (Kayles has period 12 and preperiod 71; the game $0.106$ has a period exceeding $3\times10^{11}$). For others, such as $0.007$ and $0.6$, no period has been found despite extensive computation. A disproof would exhibit a finite octal code whose nim-sequence is not eventually periodic.
--
--   **Formalization Note** Codes are arbitrary finite digit lists, including those with a nonzero $d_0$ (splitting without removing tokens); see the definition's note for the treatment of $d_0$. No bound on $n_0$ or $p$ is required.
-- source:
--   A. N. Siegel, Combinatorial Game Theory, GSM 146, AMS 2013, Section IV.2, p. 194: 'Question. Is every finite octal game eventually periodic?' (a question from Winning Ways, Berlekamp-Conway-Guy, 1982; also listed in Siegel's Appendix A). Definitions pp. 188-191.

import Mathlib
import Definitions.Def_OctalGames_Code
open OctalGames

theorem OctalGames.guy_question (c : Code) : EventuallyPeriodic c := by sorry
