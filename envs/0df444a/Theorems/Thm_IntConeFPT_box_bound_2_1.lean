-- Prove2me | Theorems.Thm_IntConeFPT_box_bound_2_1
-- name    : IntConeFPT.box_bound_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:45.21893+00:00
-- url     : https://prove2.me/theorems/d5b76773-9933-47f6-af90-a963ca10078d
-- title:
--   (2.1) — a polynomial-time computable box bound $M\ge1$ with $P^{(t)}\subseteq[-M,M]^{d+k}$
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, on every valid instance $I$ of (♣), computes an integer $M\ge1$ with
--   $$
--   P^{(t)}\subseteq[-M,M]^{d+k}\qquad\text{for all }t\in[\tau],\tag{2.1}
--   $$
--   whose binary encoding has length at most $|I|^C$, within $|I|^C$ steps.
--
--   All later steps use $M$ to bound integer coordinates and to make the residue-class searches finite.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §2, (2.1), p.6

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

/-- **(2.1): a polynomial-time computable box bound `M`.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §2, (2.1), p.6: "Since each P^(t) is bounded,
standard polyhedral theory (see, e.g., [Sch86, Theorem 10.3]) yields a polynomial-time computable
integer M ≥ 1 with enc(M) = |I|^{O(1)} such that P^(t) ⊆ [−M, M]^{d+k} ∀t ∈ [τ]."

There are a constant `C` and a Turing machine that, on every valid instance `I`, outputs (in
binary) an integer `M ≥ 1` with `P^(t) ⊆ [−M, M]^{d+k}` for every type, of encoding length at most
`|I|^C`, within `|I|^C` steps.

**Formalization Note.** `|I|` is `(encInstance I).length`; "polynomial-time" and
"enc(M) = |I|^{O(1)}" are read with one absolute exponent `C` placed before the machine. -/
theorem box_bound_2_1 :
    ∃ C : ℕ, ∃ Mtm : Machine, ∀ I : Instance, I.Valid →
      ∃ M : ℕ, 1 ≤ M ∧ (∀ t, ∀ p ∈ I.P t, InBox M p) ∧
        (encNat M).length ≤ (encInstance I).length ^ C ∧
        RunsWithin Mtm (encInstance I) (encNat M) (((encInstance I).length : ℝ) ^ C) := by sorry

end IntConeFPT
