-- Prove2me | Theorems.Thm_IntConeFPT_lemma_13
-- name    : IntConeFPT.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:20.322761+00:00
-- url     : https://prove2.me/theorems/a540645a-ecb3-4426-8161-4b5855f3a13d
-- title:
--   Lemma 13 (Integer Feasibility over $\hat K_R(\gamma)$ [Dad12]) — decide and find an integer point with a rational lift in time $2^{\tau\log(\tau+1)2^{O(d)}}(|I|+\mathrm{enc}(\gamma))^{O(1)}$
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, given a valid instance, $N_{\max}\in\mathbb Z_{\ge0}$, a candidate tuple $R$ and a rational budget $\gamma$, decides whether $\hat K_R(\gamma)$ contains an integer point and, if so, returns integers $z^{(t)}_r$, $n^{(t)}_r$ and rationals $w^{(t)}_r$ with $(z,w,n)\in K_R(\gamma)$, within
--   $$
--   2^{\tau\log_2(\tau+1)\,2^{Cd}}\cdot L^C
--   $$
--   steps, where $L$ is the length of the encoded input $(I,N_{\max},R,\gamma)$.
--
--   This is the integer-feasibility subroutine of Proposition 14; its dimension $D_R\le\tau(d+1)2^d$ is independent of $k$.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - encoding: |I| + enc(γ), where |I| includes enc(N_max) (p.11) and R is a fixed candidate tuple (§3.4) → input encInstance I ++ encNat N_max ++ encCand R ++ encRat γ, with IsCandidate R; reason: the inputs of the call written out; R is listed residue by residue
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 13, p.15

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

/-- **Lemma 13 (Integer Feasibility over `K̂_R(γ)` [Dad12]).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 13, p.15: "One can deterministically decide whether
K̂_R(γ) contains an integer point and, if so, find one together with a rational lift in K_R(γ), in
time 2^{τ log(τ+1) 2^{O(d)}} · (|I| + enc(γ))^{O(1)}."

Input: a valid instance, `N_max ∈ Z≥0` (whose encoding length is part of |I|, p.11), a candidate
tuple `R` (`|R^(t)| ≤ 2^d`; Lemma 13 is applied to these, p.16) and a rational budget `γ`. Output:
`none` exactly when `K̂_R(γ)` has no integer point; otherwise, block by block, integers `z`, `n` and
a rational `w` with `(z, w, n) ∈ K_R(γ)`.

**Formalization Note.** Machine model, encodings and the `O(·)` reading as in `RunsWithin` and
`fptBound`. -/
theorem lemma_13 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (Nmax : ℕ) (R : Cand I), IsCandidate I R → ∀ γ : ℚ,
        let inp := encInstance I ++ encNat Nmax ++ [3] ++ encCand R ++ encRat γ ++ [3]
        ∃ o : Option ((t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ),
          (o = none ↔ ¬ ∃ zn ∈ Khat I R Nmax γ, IsIntegral zn) ∧
          (∀ s, o = some s →
            (fun t i => ((fun j => ((s t i).1 j : ℝ)), (fun j => ((s t i).2.1 j : ℝ)),
              ((s t i).2.2 : ℝ))) ∈ K I R Nmax γ) ∧
          RunsWithin M inp (encLift (R := R) o) (fptBound C I.τ I.d inp.length) := by sorry

end IntConeFPT
