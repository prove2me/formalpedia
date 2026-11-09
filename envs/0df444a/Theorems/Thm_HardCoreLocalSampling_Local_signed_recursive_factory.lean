-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_signed_recursive_factory
-- name    : HardCoreLocalSampling.Local.signed_recursive_factory
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:35.744971+00:00
-- url     : https://prove2.me/theorems/d7b48d36-9f89-4911-9d59-aafac866dee9
-- title:
--   Lemma 11 — Signed recursive factory
-- statement:
--   Suppose a finite acyclic family of equations has the form $z_s=\sum_\alpha d_{s,\alpha}\prod_iz_{s_i}^{\alpha_i}$, $|z_s|\le1$, with absolute convergence on $[-1,1]^{d_s}$ and envelopes satisfying (17). Assume the envelope choices and signs of prescribed computable means are implementable. There is a recursive algorithm returning $Z_s\in\{-1,+1\}$ with $\mathbb EZ_s=z_s$, and the expected number of recursive calls, counting the initial one, is at most $1/(1-\kappa)$.
--
--   The algorithm selects $\alpha$ with probability $q_{s,\alpha}$, returns a fresh fair sign on the leftover mass, and otherwise returns $S\prod_i\prod_{j\le\alpha_i}Z^{(j)}_{s_i}$ with $S$ of mean $d_{s,\alpha}/q_{s,\alpha}$ and independent recursive signs. Repeated occurrences of a child require independent calls.
--
--   Implementability is supplied by actual programs for selection and coefficient signs, uniformly over the finite state labels and multiindices. The conclusion constructs a fair-bit program realizing the joint sign/call-count law of the recursive factory, simultaneously for every state. The call count includes the initial call and is returned in a number register. No running-time bound for implementing the primitives is assumed or asserted in this abstract lemma.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - encoding: a recursive algorithm returning Z_s with E Z_s = z_s and a bound on its recursive calls → a program implementing the joint sign/call-count law factorySign, with P(+1) = (1 + z_s)/2 and the same expected call bound; reason: the recursive bind definition specifies fresh independent calls and counts each occurrence; the program must realize that joint law and halt almost surely
--   - encoding: envelope choices and signs of prescribed computable means are implementable → SelectionImplemented and MeanSignsImplemented require fair-bit program implementations; finite states use injective natural-number labels; reason: these are operational hypotheses for the primitive choices only; every finite state family admits such labels, and no correctness or call bound of the factory is assumed
--   - generalization: the offspring bound κ := ρ + g/4 of (17) → any real κ < 1 bounding the degree-weighted mass; reason: the lemma's family has no ρ, and the proof uses only κ < 1; ρ + g/4 is an instance
--   - generalization: the rational envelopes supplied by Lemma 10 → real-valued envelopes with an implemented selection law; reason: rational envelopes are included by coercion; the abstract construction uses only their masses, budgets and implementability
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 11, eq. (21), printed p.9 (PDF p.10)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Potential
import Definitions.Def_HardCoreLocalSampling_Local_Factory

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 11, printed p.9 (PDF p.10). The hypothesis
"the envelope choices and signs of prescribed computable means are implementable" is expressed
by fair-bit program implementations of both primitives. The conclusion constructs a program
realizing the joint sign/call-count law `factorySign`. Its sign has mean `z s`, stated as
`P(+1) = (1 + z_s)/2`, and its expected number of calls, including the initial one, is at most
`1/(1-κ)`. All states are covered by one implementation, using any injective finite labeling. -/
theorem signed_recursive_factory {S : Type} [Fintype S] (deg : S → ℕ)
    (child : ∀ s, Fin (deg s) → S) (rank : S → ℕ)
    (hrank : ∀ s i, rank (child s i) < rank s)
    (z : S → ℝ) (d q : ∀ s, (Fin (deg s) → ℕ) → ℝ) (κ : ℝ)
    (hz : ∀ s, |z s| ≤ 1)
    (hconv : ∀ s (x : Fin (deg s) → ℝ), (∀ i, |x i| ≤ 1) →
      Summable fun α => |d s α * monomial x α|)
    (heq : ∀ s, z s = ∑' α, d s α * monomial (fun i => z (child s i)) α)
    (henv : ∀ s α, |d s α| ≤ q s α)
    (hQs : ∀ s, Summable (q s)) (hQ : ∀ s, ∑' α, q s α < 1)
    (hTs : ∀ s, Summable fun α => (mdeg α : ℝ) * q s α)
    (hT : ∀ s, ∑' α, (mdeg α : ℝ) * q s α ≤ κ) (hκ : κ < 1)
    (select : ∀ s, PMF (Option (Fin (deg s) → ℕ)))
    (hselect : ∀ s α, select s (some α) = ENNReal.ofReal (q s α))
    (encode : S → ℕ) (hencode : Function.Injective encode)
    (hselection : SelectionImplemented encode select)
    (hsigns : MeanSignsImplemented encode d q) :
    let laws := factorySign child select (fun s α => d s α / q s α) rank
    ∃ P : Program, FactoryImplemented encode laws P ∧
      ∀ s,
        ((laws s).map Prod.fst) true = ENNReal.ofReal ((1 + z s) / 2) ∧
        ∑' x, laws s x * (x.2 : ENNReal) ≤ ENNReal.ofReal (1 / (1 - κ)) := by sorry

end HardCoreLocalSampling.Local
