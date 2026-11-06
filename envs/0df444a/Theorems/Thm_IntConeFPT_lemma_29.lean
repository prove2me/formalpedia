-- Prove2me | Theorems.Thm_IntConeFPT_lemma_29
-- name    : IntConeFPT.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:29.487646+00:00
-- url     : https://prove2.me/theorems/c6451ac6-e9ac-467a-bde5-b79b099aa597
-- title:
--   Lemma 29 (Integer Pricing) — minimize $f(x)-\langle a,(x,u)\rangle$ over a residue class in time $2^{O(d^2\log(d+1))}(|I|+\mathrm{enc}(a))^{O(1)}$
-- statement:
--   There are a constant $C$ and a deterministic algorithm that, given a valid instance, a type $t$, a residue $r\in\{0,\dots,2^d-1\}^d$ and $a\in\mathbb Q^{d+k}$, either reports $S^{(t)}_r=\emptyset$ (exactly when it is empty) or returns a rational generator $(x^\star,u^\star)\in V^{(t)}_r$ minimizing
--   $$
--   \min_{(x,u)\in S^{(t)}_r}\big(f^{(t)}(x)-\langle a,(x,u)\rangle\big)
--   $$
--   over all of $S^{(t)}_r$, whose encoding length is at most $|I|^C$, within $2^{C d^2\log_2(d+1)}\cdot L^C$ steps, where $L$ is the length of the encoded input $(I,t,r,a)$.
--
--   This pricing step is the oracle behind Lemmas 5 and 12.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - encoding: (B.1 fixes a type t) given r and a → input (I, t, r, a) encoded as encLocal I t r ++ encVec a_x ++ encVec a_u; reason: the type is part of the call; |I| + enc(a) is the input length up to separators
--   - encoding: r ∈ {0, …, 2^d − 1}^d → r : Fin d → Fin (2^d) (Residue d); reason: Lean convention; same residues
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 29, p.33 (Section B.1)

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

/-- **Lemma 29 (Integer Pricing).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 29, p.33: "Given r ∈ {0, …, 2^d − 1}^d and a ∈ Q^{d+k},
one can determine that S_r = ∅ or return a rational minimizer of
min_{(x,u)∈S_r} (f(x) − ⟨a, (x, u)⟩) deterministically in time
2^{O(d² log(d+1))} · (|I| + enc(a))^{O(1)}. The returned point can be chosen in V_r and has encoding
length polynomial in |I|."

There are a constant `C` and a machine that, given a valid instance, a type `t` (B.1 fixes one),
a residue `r` and `a = (a_x, a_u) ∈ Q^d × Q^k`, outputs `none` exactly when `S_r^(t) = ∅`, and
otherwise a rational generator in `V_r^(t)` minimizing `f^(t)(x) − ⟨a, (x, u)⟩` over all of
`S_r^(t)` (real `u`), of encoding length at most `|I|^C`, within `2^{C d² log₂(d+1)} · L^C` steps,
`L` the input length.

**Formalization Note.** Machine model, encodings and the `O(·)` reading as in `RunsWithin` and
`oracleBound`. The input `(I, t, r, a)` is `encLocal I t r ++ encVec a_x ++ encVec a_u`. -/
theorem lemma_29 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (ax : Fin I.d → ℚ) (au : Fin I.k → ℚ),
        let inp := encLocal I t r ++ encVec ax ++ encVec au
        ∃ o : Option ((Fin I.d → ℤ) × (Fin I.k → ℚ)),
          (o = none ↔ I.Sr t r = ∅) ∧
          (∀ g, o = some g →
            ratGen g.1 g.2 ∈ I.Vr t r ∧
            (∀ g' ∈ I.Sr t r,
              I.f t (fun i => (g.1 i : ℝ)) - pairing (ratPair ax au) (ratGen g.1 g.2).toReal ≤
                I.f t (fun i => (g'.1 i : ℝ)) - pairing (ratPair ax au) g'.toReal) ∧
            (encGen g.1 g.2).length ≤ (encInstance I).length ^ C) ∧
          RunsWithin M inp (encPricing o) (oracleBound C I.d inp.length) := by sorry

end IntConeFPT
