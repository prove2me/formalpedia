-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_size_toData_le
-- name    : MIPRE.Cost.Machine.size_toData_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:37.918145+00:00
-- url     : https://prove2.me/theorems/3606237b-7d9e-473e-bc06-eba4eb057fe4
-- title:
--   Encoded size of a bounded machine configuration is at most $\mathrm{cfgSizeBound}(V, L, P, K)$
-- statement:
--   Configurations of the evaluation machine of the ambient cost model (`MIPRE.Cost.Machine`; see `eval_steps_bound` for the machine) are encoded as data (`Cfg.toData`) so that the self-interpreter can operate on them. Data are binary trees built from $\mathrm{nil}$ and $\mathrm{cons}$, with $\mathrm{size}$ the number of nodes ($\mathrm{size}(\mathrm{nil}) = 1$); a list of data is encoded as the $\mathrm{cons}$-chain of its elements ending in $\mathrm{nil}$ ($\mathrm{list}$, `Data.list`), a program $p$ by its syntax tree, of size $\|p\|$, and the unary numeral $\underline j$ (`Data.ofNat j`) has size $2j + 1$. The encoding of a configuration $\langle \gamma, \rho, \kappa\rangle$ is
--
--   $$
--   \mathrm{toData}\langle \gamma, \rho, \kappa\rangle = \mathrm{cons}\bigl(\mathrm{enc}(\gamma),\ \mathrm{cons}(\mathrm{list}(\rho),\ \mathrm{list}(\mathrm{enc}(\kappa)))\bigr),
--   $$
--
--   where the control $\mathrm{ev}\,p$ is encoded as $\mathrm{cons}(\mathrm{nil}, \mathrm{enc}(p))$ and $\mathrm{ret}\,v$ as $\mathrm{cons}(\mathrm{cons}(\mathrm{nil},\mathrm{nil}), v)$, and a frame as $\mathrm{cons}(\underline j, \mathrm{payload})$ with the tag $\underline 0, \underline 1, \underline 2, \underline 3$ for $\mathrm{cons}_1(q,\rho)$, $\mathrm{cons}_2(a)$, $\mathrm{let}_1(b,\rho)$, $\mathrm{loop}_1(b,\rho)$ respectively, and payload $\mathrm{cons}(\mathrm{enc}(q), \mathrm{list}(\rho))$, resp. $a$, resp. $\mathrm{cons}(\mathrm{enc}(b), \mathrm{list}(\rho))$.
--
--   Recall that $\mathrm{CfgBound}(V, L, P, K, c)$ means: a returned value of $c$ has size at most $V$, a program under evaluation has encoded size at most $P$, the environment has length at most $L$ with values of size at most $V$, the stack has at most $K$ frames, and each frame's program, environment and value obey the same bounds $P$, $L$ (with values at most $V$) and $V$. Define
--
--   $$
--   \mathrm{cfgSizeBound}(V, L, P, K) = V + P + LV + L + K\,(V + P + LV + L + 10) + K + 8.
--   $$
--
--   **Theorem.** If $\mathrm{CfgBound}(V, L, P, K, c)$, then
--
--   $$
--   \mathrm{size}\bigl(\mathrm{toData}(c)\bigr) \le \mathrm{cfgSizeBound}(V, L, P, K).
--   $$
--
--   Together with `eval_steps_bound`, which bounds every configuration along the run simulating a derivation of cost $t$ by $(V, L + 2t, P, K + t)$, this makes every encoded configuration of such a run polynomially bounded in the size of the program, the size of the input and the cost. The proof of the efficient universal machine (blueprint `lem:universal-tm`, in `MIPRE.Foundations.Cost.Universal`) takes $V = L = P = K = X$ with $X = \|c\| + \mathrm{size}(v) + t$ for a program $c$ run on $v$ at cost $t$, so that $L + 2t \le 3X$ and $K + t \le 2X$, and uses $\sigma(X) = \mathrm{cfgSizeBound}(X, 3X, X, 2X)$ (`sigmaFun`), a cubic polynomial in $X$, as the bound on the input of every call to the step program in the self-interpreter and in the size guard of the clocked universal machine.
--
--   **Formalization Note** The bound is a closed-form polynomial obtained by adding up the components of the encoding: the control contributes at most $V + P + 4$ (the sum of the two cases $\|p\| + 2$ and $\mathrm{size}(v) + 4$, rather than their maximum); the environment chain at most $LV + L + 1$, since a $\mathrm{cons}$-chain of at most $L$ values of size at most $V$ has size at most $LV + L + 1$ (`size_list_le_of_forall`); each frame at most $V + P + LV + L + 10$ (`frame_size_le`, where $10$ accounts for the largest tag $\underline 3$, of size $7$, and three $\mathrm{cons}$ nodes); the stack chain therefore at most $K(V + P + LV + L + 10) + K + 1$; plus the two outer $\mathrm{cons}$ nodes. It holds for every bounded configuration, not only for those arising along runs.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineBound.lean#L426-L447; internal lemma of the formalization of blueprint lem:universal-tm (via the self-interpreter), https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.1

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine

theorem MIPRE.Cost.Machine.size_toData_le {V L P K : ℕ} {c : Cfg} (h : CfgBound V L P K c) :
    (Cfg.toData c).size ≤ cfgSizeBound V L P K := by sorry
