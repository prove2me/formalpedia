-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_halts_iff
-- name    : MIPRE.Cost.Machine.halts_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:13.602495+00:00
-- url     : https://prove2.me/theorems/772d6b5b-5a20-471a-8ca5-aca3c32a3ce6
-- title:
--   A program halts with a value if and only if the evaluation machine reaches a final configuration with that value
-- statement:
--   The *evaluation machine* (`Machine`) is a small-step, CEK-style machine for the ambient language of the cost model. A configuration $\langle \kappa, \rho, k \rangle$ (`Cfg`) consists of a control $\kappa$, which is either $\mathtt{ev}\,p$ ("evaluate the program $p$") or $\mathtt{ret}\,v$ ("return the value $v$"), an environment $\rho$ (a list of data, variable $0$ first) and a stack $k$ of continuation frames: $\mathtt{cons1}(t, \rho)$ (the head of a $\mathtt{cons}$ is being evaluated; evaluate $t$ in $\rho$ next), $\mathtt{cons2}(a)$ (the head value is $a$; return $\mathtt{cons}(a, \cdot)$ next), $\mathtt{let1}(b, \rho)$ and $\mathtt{loop1}(b, \rho)$. The step function $\mathrm{step}$ (`step`) is total and deterministic, and it leaves *final* configurations $\langle \mathtt{ret}\,v, \rho, [] \rangle$ unchanged. Each configuration is charged a cost $\mathrm{stepCost}$: a configuration $\langle \mathtt{ev}\,p, \rho, k\rangle$ is charged the unit of the evaluation rule for the head constructor of $p$ — $\mathrm{size}(\rho(i)) + 1$ for $\mathtt{var}\ i$, $1$ for $\mathtt{nil}$, $\mathrm{size}(d)$ for $\mathtt{const}\ d$, $1$ for $\mathtt{cons}$, $\mathtt{elim}$ and $\mathtt{let}$, and $0$ for $\mathtt{loop}$, whose unit is charged instead when the value of the body is dispatched at a $\mathtt{loop1}$ frame; all other returns cost $0$. Write $\mathrm{cost}(c, N) = \sum_{i < N} \mathrm{stepCost}(\mathrm{step}^i(c))$ (`costSum`) for the cost accumulated over $N$ steps, and $\mathrm{Steps}(c, N, c', t)$ (`Steps`) for "$\mathrm{step}^N(c) = c'$ and $\mathrm{cost}(c, N) = t$". The big-step semantics $\rho \vdash p \Downarrow_t r$ (`Eval`) is the timed evaluation relation that the machine implements: $p$ in the environment $\rho$ halts with result $r$ at cost $t$. For a program $p$ and an input $x$, write $p(x) \Downarrow_t r$ (`p.Runs x r t`) for $[x] \vdash p \Downarrow_t r$.
--
--   **Statement.** For every program $p$ and data $x, r$:
--
--   $$ \bigl(\exists t,\ p(x) \Downarrow_t r\bigr) \iff \bigl(\exists N, e,\ \mathrm{step}^{N}\langle \mathtt{ev}\,p, [x], [] \rangle = \langle \mathtt{ret}\,r, e, [] \rangle\bigr). $$
--
--   This combines the two directions of the derivation–machine correspondence at the initial configuration of a program on its input. It is the form consumed by the soundness of the self-interpreter (`univProg_halts_of`, blueprint `lem:universal-tm`) and by the proof that evaluation is partial recursive (`mem_evalData_iff`), which transports it along the encoding of configurations as data.
--
--   **Formalization Note**: The left side is the halting predicate of the big-step semantics with an unspecified cost, and the right side mentions only the step function iterated on `Cfg`, with the environment $e$ of the final configuration existential; costs play no role in this statement.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Machine.lean#L331-L346; internal lemma of the formalization of blueprint lem:universal-tm (via the self-interpreter)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Machine

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine

theorem MIPRE.Cost.Machine.halts_iff (p : Prog) (x r : Data) :
    (∃ t, p.Runs x r t) ↔ ∃ N e, step^[N] ⟨.ev p, [x], []⟩ = ⟨.ret r, e, []⟩ := by sorry
