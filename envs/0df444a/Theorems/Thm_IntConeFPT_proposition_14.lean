-- Prove2me | Theorems.Thm_IntConeFPT_proposition_14
-- name    : IntConeFPT.proposition_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:51.675354+00:00
-- url     : https://prove2.me/theorems/47a5bab0-21d7-4a26-a40f-76c96708555e
-- title:
--   Proposition 14 (Optimization with a Multiplicity Bound) — solve (♣)+(1.1) in time $2^{\tau\log(\tau+1)2^{O(d)}}|I|^{O(1)}$ with $\le2^{2d+1}$ generators per type
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, given a valid instance and $N_{\max}\in\mathbb Z_{\ge0}$, either reports that no $\lambda$ is feasible for (♣) subject to $\sum_tN^{(t)}\le N_{\max}$ (1.1) (exactly when this holds), or returns an aggregate $(y,v)$ and a certificate of rational generators with positive integer multiplicities, at most $2^{2d+1}$ distinct generators per type, that is feasible subject to (1.1), has total aggregate $(y,v)$, and has cost at most that of every $\lambda$ feasible subject to (1.1); within
--   $$
--   2^{\tau\log_2(\tau+1)\,2^{Cd}}\cdot L^C
--   $$
--   steps, where $L$ is the length of the encoded input $(I,N_{\max})$.
--
--   Theorem 1 calls this twice with $N_{\max}=N_\star$.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - encoding: returns an optimum with at most 2^{2d+1} generators per type → Output.optimal y v cert with CertOK (≤ 2^{2d+1} distinct generators, multiplicities ≥ 1) and its aggregate (y, v); reason: the optimum is its certificate; the aggregate is computed from it
--   - encoding: |I| includes enc(N_max) (p.11) → input encInstance I ++ encNat N_max ++ [3]; reason: the inputs of the call written out
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Proposition 14, p.16

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

/-- **Proposition 14 (Optimization with a Multiplicity Bound).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Proposition 14, p.16: "Given N_max ∈ Z≥0, one can solve (♣)
subject to (1.1) deterministically in time 2^{τ log(τ+1) 2^{O(d)}} · |I|^{O(1)}. The algorithm reports
infeasibility or returns an optimum with at most 2^{2d+1} generators per type."

On input `(I, N_max)` the machine outputs `infeasible` exactly when no `λ` is feasible with
`Σ_t N^(t) ≤ N_max`, and otherwise an optimal aggregate with a certificate (rational generators,
positive integer multiplicities, at most `2^{2d+1}` distinct generators per type) whose cost is at
most that of every `λ` feasible subject to (1.1) (`Output.CorrectN`).

**Formalization Note.** Machine model, encodings and the `O(·)` reading as in `RunsWithin` and
`fptBound`; |I| includes `enc(N_max)` (p.11). -/
theorem proposition_14 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid → ∀ Nmax : ℕ,
      let inp := encInstance I ++ encNat Nmax ++ [3]
      ∃ o : Output I, o.CorrectN Nmax ∧
        RunsWithin M inp (encOutput o) (fptBound C I.τ I.d inp.length) := by sorry

end IntConeFPT
