-- Prove2me | Theorems.Thm_IntConeFPT_lemma_6
-- name    : IntConeFPT.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:12.500464+00:00
-- url     : https://prove2.me/theorems/cdd612ea-d891-4f2e-8f35-1e790795e78e
-- title:
--   Lemma 6 (Constructive Residue Decomposition) — integer decomposition with $\le2^{d+1}-1$ distinct generators and cost $\le\Phi_r$
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, given a valid instance, a type $t$, a residue $r$ and a rational point $(z_r,w_r,n_r)\in C^{(t)}_r$ with $z_r\in\mathbb Z^d$ and $n_r\in\mathbb Z_{\ge0}$, returns $p\le2^{d+1}-1$ pairwise distinct generators $(x_j,u_j)\in P^{(t)}_r\cap(\mathbb Z^d\times\mathbb Q^k)$ (hence in $S^{(t)}$) with positive integer coefficients $\lambda_j$ such that
--   $$
--   (z_r,w_r)=\sum_{j=1}^p\lambda_j(x_j,u_j),\qquad\sum_{j=1}^p\lambda_j=n_r,\qquad\sum_{j=1}^p\lambda_jf^{(t)}(x_j)\le\Phi^{(t)}_r(z_r,w_r,n_r),
--   $$
--   within $2^{Cd^2\log_2(d+1)}\cdot L^C$ steps, where $L$ is the length of the encoded input $(I,t,r,z_r,w_r,n_r)$.
--
--   The generators lie in the residue hull $P^{(t)}_r$ and need not have residue $r$. This converts integer points of the formulation into actual solutions of (♣).
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - encoding: an integer conic decomposition with p distinct generators and coefficients λ_j → a list of (x_j, u_j, λ_j) with pairwise distinct (x_j, u_j), λ_j ≥ 1, length ≤ 2^(d+1) − 1; reason: Lean convention; same objects
--   - encoding: r ∈ {0, …, 2^d − 1}^d → r : Fin d → Fin (2^d) (Residue d); reason: Lean convention; same residues
--   - encoding: the finite value Φ_r^(t)(z, w, n) → Instance.Phi valued in EReal, compared with a cast real; reason: Φ is finite on C_r; no EReal arithmetic is used
--   - encoding: time in |I| + enc(z_r, w_r, n_r), with a fixed type t and a residue r → the input length of encLocal I t r followed by the query; reason: the inputs of the call written out; a valid instance has at least one row per type, so enc(t, r) is polynomial in |I|
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 6, p.9 (restated with proof, Section B.2, p.37)

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

/-- **Lemma 6 (Constructive Residue Decomposition).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 6, p.9 (restated with proof p.37): "Given a residue vector
r ∈ {0, …, 2^d − 1}^d and a rational point (z_r, w_r, n_r) ∈ C_r^(t) with z_r ∈ Z^d and
n_r ∈ Z≥0, an integer conic decomposition (z_r, w_r) = Σ_{j=1}^p λ_j (x_j, u_j),
Σ_{j=1}^p λ_j = n_r, with p ≤ 2^{d+1} − 1 distinct generators (x_j, u_j) ∈ P_r^(t) ∩ (Z^d × Q^k)
⊆ S^(t) and positive integer coefficients λ_j ∈ Z>0, satisfying
Σ_{j=1}^p λ_j f^(t)(x_j) ≤ Φ_r^(t)(z_r, w_r, n_r), can be computed in time
2^{O(d² log(d+1))} · (|I| + enc(z_r, w_r, n_r))^{O(1)}."

The generators lie in the residue hull `P_r^(t)` (not necessarily in the class `S_r^(t)`), hence in
`S^(t)`.

**Formalization Note.** Machine model, encodings and the `O(·)` reading as in `RunsWithin` and
`oracleBound`. The decomposition is a list of entries `(x_j, u_j, λ_j)`, encoded by `encCert`. -/
theorem lemma_6 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ),
        ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), (n : ℝ)) ∈ I.Cr t r →
        let inp := encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]
        ∃ out : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ),
          out.length ≤ 2 ^ (I.d + 1) - 1 ∧
          (out.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ out, 1 ≤ e.2.2 ∧ (certGen e).toReal ∈ I.Pr t r ∧ certGen e ∈ I.S t) ∧
          (out.map fun e => (e.2.2 : ℝ) • (certGen e).toReal).sum =
            ((fun i => (z i : ℝ)), fun j => (w j : ℝ)) ∧
          (out.map fun e => e.2.2).sum = n ∧
          (((out.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum : ℝ) : EReal) ≤
            I.Phi t r ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), (n : ℝ)) ∧
          RunsWithin M inp (encCert out) (oracleBound C I.d inp.length) := by sorry

end IntConeFPT
