-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_finite_queries
-- name    : ObfImpossibility.RiceNoSize.finite_queries
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:59.545204+00:00
-- url     : https://prove2.me/theorems/77e849be-4e4c-43d3-82ce-3e3a01e1965e
-- title:
--   Proof of Thm A.4, p. A:42 — a halting run $S^{\langle M_0\rangle}()$ only sees queries with $t,|x|\le n$
-- statement:
--   Let $S$ be an oracle machine and $M_0$ a machine such that $S^{\langle M_0\rangle}()$ halts with output $\sigma$. Then there is an $n$ bounding $t$ and $|x|$ over the queries $(1^t,x)$ that matter, in the following sense: for every machine $M$,
--   $$\Big(\forall t,x\le n:\ \langle M\rangle(1^t,x)=\langle M_0\rangle(1^t,x)\Big)\;\Longrightarrow\; S^{\langle M\rangle}()=\sigma .$$
--
--   In the proof of Theorem A.4 this is applied with $M_0=Z$ and $\sigma=0$: the halting run of $S$ on $Z$ asks only finitely many queries, so any machine with the same bounded behaviour on those queries receives the same answer from $S$.
--
--   **Formalization Note** The statement holds for every oracle program and every machine; it is the "use principle" of oracle computation specialised to the oracle $\langle\cdot\rangle$. Queries are coded as `Nat.pair t x`.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 ("Let n be an upper bound on |x| and t over all oracle queries (1^t, x) of S^⟨Z⟩().")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- p. A:42: a halting run `S^{⟨M₀⟩}() = σ` makes oracle queries `(1^t, x)` with `t` and `|x|`
bounded by some `n`; hence every machine `M` with `⟨M⟩(1^t, x) = ⟨M₀⟩(1^t, x)` for all
`t, |x| ≤ n` also has `S^{⟨M⟩}() = σ`. -/
theorem finite_queries (S : FriedbergMuchnik.Program) (M₀ : Machine) (σ : ℕ)
    (h : simRun S M₀ = Part.some σ) :
    ∃ n : ℕ, ∀ M : Machine,
      (∀ t x : ℕ, t ≤ n → x ≤ n → bounded M t x = bounded M₀ t x) →
      simRun S M = Part.some σ := by sorry

end ObfImpossibility.RiceNoSize
