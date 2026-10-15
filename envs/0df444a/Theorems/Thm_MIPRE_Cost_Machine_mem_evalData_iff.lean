-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_mem_evalData_iff
-- name    : MIPRE.Cost.Machine.mem_evalData_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:15.530439+00:00
-- url     : https://prove2.me/theorems/edf441f8-0c97-462a-9a2d-1238fd93c478
-- title:
--   Evaluation as a partial recursive function on data agrees with the big-step semantics
-- statement:
--   The evaluation machine of the ambient cost model has configurations $\langle \kappa, \rho, k\rangle$ (a control $\mathtt{ev}\,p$ or $\mathtt{ret}\,v$, an environment and a stack of frames), a total step function $\mathrm{step}$ fixing the final configurations $\langle \mathtt{ret}\,r, e, []\rangle$, and it implements the big-step semantics: writing $p(x) \Downarrow_t r$ for "the program $p$ on input $x$ halts with result $r$ at cost $t$", one has $p(x) \Downarrow_t r$ for some $t$ iff $\mathrm{step}^N\langle \mathtt{ev}\,p, [x], []\rangle = \langle \mathtt{ret}\,r, e, []\rangle$ for some $N, e$ (`halts_iff`). To connect with Mathlib's computability, configurations are encoded as data (`Cfg.toData`): a control is $\mathtt{cons}(\mathtt{nil}, \mathrm{enc}(p))$ or $\mathtt{cons}(\mathtt{cons}(\mathtt{nil},\mathtt{nil}), v)$, a configuration is $\mathtt{cons}(\text{control}, \mathtt{cons}(\text{environment}, \text{stack}))$ with the environment and the stack as $\mathtt{cons}$-chains, and frames carry unary tags. On data, $\mathrm{stepData}$ is defined by first-order tree operations alone and agrees with the machine, $\mathrm{stepData}(\mathrm{enc}(c)) = \mathrm{enc}(\mathrm{step}(c))$ (`stepData_toData`); $\mathrm{IsFinalD}(d)$ tests finality on data, $\mathrm{resultD}(d)$ reads the returned value, and $\mathrm{initData}(p, x)$ is the encoding of the initial configuration $\langle \mathtt{ev}\,p, [x], [] \rangle$ for an encoded program $p$. Evaluation on data is the partial function
--
--   $$ \mathrm{evalData}(p, x) := \mathrm{fix}\Bigl(d \mapsto \begin{cases} \mathrm{inl}(\mathrm{resultD}(d)) & \text{if } \mathrm{IsFinalD}(d) \\ \mathrm{inr}(\mathrm{stepData}(d)) & \text{otherwise}\end{cases}\Bigr)\bigl(\mathrm{initData}(p,x)\bigr) \;\in\; \mathrm{Part}\,\mathrm{Data}, $$
--
--   the `PFun.fix` of one iteration of the evaluation loop (`evalStep`); it is partial recursive (`partrec_evalData`) because the step on data is primitive recursive.
--
--   **Statement.** For every program $c$ and data $x, r$,
--
--   $$ r \in \mathrm{evalData}(\mathrm{enc}(c), x) \iff \exists t,\ c(x) \Downarrow_t r . $$
--
--   Together with `partrec_evalData`, this is the bridge from the ambient model to Mathlib's computability: a polynomial-time function of the model, precomposed with a computable encoding of its input, has a computable encoded output (`PolyTimeFun.computable_encode_comp`, `computable_comp`), which is how the reductions of the halting form of the compression lemmas (blueprint `lem:halting-form`: `recursive_compression_halting`, `compressibility_criterion_halting`) are shown `Computable`.
--
--   **Formalization Note**: Membership $r \in \mathrm{evalData}(\cdot)$ is Mathlib's `Part` membership (the value is defined and equals $r$); the program enters as its serialization `c.toData`, and no `Primcodable` instance for `Prog` is involved — everything is at the level of `Data`, which is denumerable through Cantor pairing. No cost information survives the transport: the right-hand side is halting with an unspecified cost.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Partrec.lean#L222-L235; internal lemma of the formalization of blueprint lem:halting-form (the bridge from the ambient model to Mathlib's computability)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Partrec

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Primrec

theorem MIPRE.Cost.Machine.mem_evalData_iff (c : Prog) (x r : Data) :
    r ∈ evalData c.toData x ↔ ∃ t, c.Runs x r t := by sorry
