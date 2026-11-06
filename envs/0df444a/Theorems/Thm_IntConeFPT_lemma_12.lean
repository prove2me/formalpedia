-- Prove2me | Theorems.Thm_IntConeFPT_lemma_12
-- name    : IntConeFPT.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:47.764529+00:00
-- url     : https://prove2.me/theorems/c465e92f-edf2-4668-a1de-dbe648ca6c4d
-- title:
--   Lemma 12 (Strong Separation for Residue Hulls) — separation over $P_r=\operatorname{conv}(S_r)$ in time $2^{O(d^2\log(d+1))}(|I|+\mathrm{enc}(x,u))^{O(1)}$
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, given a valid instance, a type $t$, a residue $r$ and a query $(x,u)\in\mathbb Q^{d+k}$, either certifies $(x,u)\in P^{(t)}_r$ or returns $c\in\mathbb Q^{d+k}$ and $\beta\in\mathbb Q$ with
--   $$
--   \langle c,(x',u')\rangle\le\beta<\langle c,(x,u)\rangle\qquad\text{for every }(x',u')\in P^{(t)}_r,
--   $$
--   with output length at most $L^C$, within $2^{Cd^2\log_2(d+1)}\cdot L^C$ steps, where $L$ is the length of the encoded input $(I,t,r,x,u)$.
--
--   It supplies the cone-membership cuts of the separation oracle in Lemma 13.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - reading: a strong separation oracle (defined on p.7: "The encoding length of its output is bounded by a fixed polynomial in the input and query lengths") → the output length bound (encSeparation o).length ≤ L^C is part of the statement; reason: Lemma 12 claims a strong separation oracle, and p.7 includes the output-length bound in that notion
--   - encoding: r ∈ {0, …, 2^d − 1}^d → r : Fin d → Fin (2^d) (Residue d); reason: Lean convention; same residues
--   - encoding: time in |I| + enc(x, u), with a fixed type t and a residue r → the input length of encLocal I t r followed by the query; reason: the inputs of the call written out; a valid instance has at least one row per type, so enc(t, r) is polynomial in |I|
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 12, p.14

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

/-- **Lemma 12 (Strong Separation for Residue Hulls).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 12, p.14: "For r ∈ {0, …, 2^d − 1}^d, a strong separation
oracle for P_r = conv(S_r) can be implemented deterministically in time
2^{O(d² log(d+1))} · (|I| + enc(x, u))^{O(1)} per query (x, u) ∈ Q^{d+k}. It either certifies
(x, u) ∈ P_r or returns c ∈ Q^{d+k} and β ∈ Q satisfying ⟨c, (x′, u′)⟩ ≤ β < ⟨c, (x, u)⟩ for every
(x′, u′) ∈ P_r."

The output is `none` (certifying `(x, u) ∈ P_r^(t)`) or `(c, β)` with `β < ⟨c, (x, u)⟩` and
`⟨c, p⟩ ≤ β` for every `p ∈ P_r^(t)`. Its encoding length is polynomial in the input and query
lengths, as the definition of a strong separation oracle requires (p.7).

**Formalization Note.** Machine model, encodings and the `O(·)` reading as in `RunsWithin` and
`oracleBound`; the input is `(I, t, r, x, u)` (Lemma 12 fixes a type, p.14). -/
theorem lemma_12 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (x : Fin I.d → ℚ) (u : Fin I.k → ℚ),
        let inp := encLocal I t r ++ encVec x ++ encVec u
        ∃ o : Option (((Fin I.d → ℚ) × (Fin I.k → ℚ)) × ℚ),
          (o = none → ratPair x u ∈ I.Pr t r) ∧
          (∀ cb, o = some cb →
            (cb.2 : ℝ) < pairing (ratPair cb.1.1 cb.1.2) (ratPair x u) ∧
            ∀ p ∈ I.Pr t r, pairing (ratPair cb.1.1 cb.1.2) p ≤ cb.2) ∧
          (encSeparation o).length ≤ inp.length ^ C ∧
          RunsWithin M inp (encSeparation o) (oracleBound C I.d inp.length) := by sorry

end IntConeFPT
