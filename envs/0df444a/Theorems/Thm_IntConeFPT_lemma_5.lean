-- Prove2me | Theorems.Thm_IntConeFPT_lemma_5
-- name    : IntConeFPT.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:00.862718+00:00
-- url     : https://prove2.me/theorems/1d253eb9-bf6a-4342-9219-c48493a2e35c
-- title:
--   Lemma 5 (Fractional Cost Oracle) — $\Phi_r$, an optimal dual pair, and an optimal representation on $\le\min\{2^d,d+k+1\}$ generators
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, given a valid instance, a type $t$, a residue $r$ with $S^{(t)}_r\ne\emptyset$, and a rational point $(z,w,n)\in C^{(t)}_r$, returns
--
--   1. the value $\varphi=\Phi^{(t)}_r(z,w,n)$ (a rational number);
--   2. a pair $(a^\star,b^\star)\in D^{(t)}_r$ with $\varphi=\langle a^\star,(z,w)\rangle+b^\star n$;
--   3. pairwise distinct rational generators $(x_i,u_i)\in S^{(t)}_r$, at most $\min\{2^d,d+k+1\}$ of them, with positive rational multiplicities $\theta_i$ such that
--   $$
--   \sum_i\theta_i=n,\qquad\sum_i\theta_i(x_i,u_i)=(z,w),\qquad\sum_i\theta_if^{(t)}(x_i)=\varphi,
--   $$
--
--   with total output length at most $L^C$, within $2^{Cd^2\log_2(d+1)}\cdot L^C$ steps, where $L$ is the length of the encoded input $(I,t,r,z,w,n)$.
--
--   Lemma 6 rounds this representation to integer multiplicities, and Lemma 13 uses the dual pair as a cut.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - generalization: the generators and their multiplicities have polynomial encoding length in the input and query → (encOracle o).length ≤ L^C for the whole output, including the value and the dual pair; reason: the proof on p.35 bounds the dual pair too, and the bound on generators and multiplicities is the sub-list of this one
--   - encoding: a fractional representation supported on at most min{2^d, d + k + 1} generators → a duplicate-free list of (x, u, θ) with θ > 0 and length ≤ min (2^d) (d + k + 1); reason: a finitely supported θ is the list of its support with positive values
--   - encoding: r ∈ {0, …, 2^d − 1}^d → r : Fin d → Fin (2^d) (Residue d); reason: Lean convention; same residues
--   - encoding: the finite value Φ_r^(t)(z, w, n) → Instance.Phi valued in EReal, compared with a cast real; reason: Φ is finite on C_r; no EReal arithmetic is used
--   - encoding: time in |I| + enc(z, w, n), with a fixed type t and a residue r → the input length of encLocal I t r followed by the query; reason: the inputs of the call written out; a valid instance has at least one row per type, so enc(t, r) is polynomial in |I|
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 5, p.9 (restated with proof, Section B.1, p.35)

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

/-- **Lemma 5 (Fractional Cost Oracle).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 5, p.9 (restated with proof p.35): "Given a nonempty residue
class S_r^(t) and a rational point (z, w, n) ∈ C_r^(t), one can compute Φ_r^(t)(z, w, n), an optimal
dual solution (a⋆, b⋆) to (3.1b) satisfying Φ_r^(t)(z, w, n) = ⟨a⋆, (z, w)⟩ + b⋆n, and a fractional
representation of (z, w, n) attaining Φ_r^(t)(z, w, n), supported on at most min{2^d, d + k + 1}
rational generators in S_r^(t), in time 2^{O(d² log(d+1))} · (|I| + enc(z, w, n))^{O(1)}. The
generators and their multiplicities have polynomial encoding length in the input and query."

The output is `(φ, (a⋆, b⋆), rep)`: the rational value `φ = Φ_r^(t)(z, w, n)`, a dual pair in
`D_r^(t)` attaining it, and a list `rep` of pairwise distinct rational generators of `S_r^(t)` with
positive rational multiplicities `θ`, at most `min{2^d, d + k + 1}` of them, with
`Σ θ = n`, `Σ θ (x, u) = (z, w)` and `Σ θ f^(t)(x) = φ`.

**Formalization Note.** Machine model, encodings and the `O(·)` reading as in `RunsWithin` and
`oracleBound`; the polynomial encoding length of the output is `(encOracle o).length ≤ L^C`. -/
theorem lemma_5 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n : ℚ),
        (I.Sr t r).Nonempty →
        ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∈ I.Cr t r →
        let inp := encLocal I t r ++ encVec z ++ encVec w ++ encRat n ++ [3]
        ∃ o : ℚ × ((Fin I.d → ℚ) × (Fin I.k → ℚ)) × ℚ × List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ),
          ((o.1 : ℝ) : EReal) = I.Phi t r ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∧
          (ratPair o.2.1.1 o.2.1.2, (o.2.2.1 : ℝ)) ∈ I.Dr t r ∧
          (o.1 : ℝ) = pairing (ratPair o.2.1.1 o.2.1.2) (ratPair z w) + (o.2.2.1 : ℝ) * n ∧
          o.2.2.2.length ≤ min (2 ^ I.d) (I.d + I.k + 1) ∧
          (o.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2) ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = n ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = o.1 ∧
          (encOracle o).length ≤ inp.length ^ C ∧
          RunsWithin M inp (encOracle o) (oracleBound C I.d inp.length) := by sorry

end IntConeFPT
