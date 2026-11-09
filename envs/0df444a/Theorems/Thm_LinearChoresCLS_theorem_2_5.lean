-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_2_5
-- name    : LinearChoresCLS.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:02.55033+00:00
-- url     : https://prove2.me/theorems/8f342c05-fc8c-44d9-8dbf-5187f27b93e7
-- title:
--   Theorem 2.5 — the ε-quadratic-KKT problem is CLS-complete (Fearnley et al. 2024)
-- statement:
--   The $\varepsilon$-quadratic-KKT problem (Definition 2.4) is CLS-complete: for some fixed exponent $k$, the problem with answers of encoding length at most $(|x|+1)^k+k$ lies in CLS, and every problem in CLS reduces to the $\varepsilon$-quadratic-KKT problem by a polynomial-time search reduction.
--
--   This is the cited starting point of the hardness proof (Fearnley, Goldberg, Hollender and Savani, 2024, Theorem 2.1 and Lemma A.1).
--
--   **Formalization Note** CLS is the public class `InCLS` (TFNP plus a polynomial-time Levin reduction to 3D-Continuous-Localopt); `CLSHard` asks for a reduction from every CLS problem. Hardness is stated for the answer relation without a length bound: the reduction's decoder must work for every $\varepsilon$-KKT point of any encoding length.
--
--   Differences from the source:
--   - reading: "CLS-complete" → (∃ k, InCLS (bounded epsQKKTSearch k)) ∧ CLSHard epsQKKTSearch; reason: membership needs a polynomial answer bound; hardness is stated for every ε-KKT point of any length, the stronger of the two hardness readings and the one the proof of Theorem 1.1 composes with
--   - encoding: an instance (A, c, ε) with rational data → binary self-delimiting encoding encQuadratic (A, c) ++ encRat ε with n ≥ 1; reason: the public encoders; n ≥ 1 is the paper's [k] for positive k
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 2.5, p.7 (cited: Fearnley, Goldberg, Hollender, Savani 2024, Theorem 2.1, Lemma A.1)

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Theorem 2.5** (arXiv:2611.06589, held version sha256 85d34a9e…, p.7; cited from Fearnley,
Goldberg, Hollender and Savani 2024, Theorem 2.1 and Lemma A.1): the ε-quadratic-KKT problem is
CLS-complete. Membership: for some fixed answer-length exponent `k`, `bounded epsQKKTSearch k` is in
CLS. Hardness: every CLS problem reduces to `epsQKKTSearch`.

**Formalization Note.** CLS is the public class `InCLS` (TFNP plus a polynomial-time search
reduction to 3D-Continuous-Localopt). Hardness is stated for the answer relation without a length
bound: the reduction's decoder must work for every ε-KKT point of any encoding length, which is
the form the reduction of Theorem 1.1 composes with. -/
theorem theorem_2_5 :
    (∃ k : ℕ, InCLS (bounded epsQKKTSearch k)) ∧ CLSHard epsQKKTSearch := by sorry

end LinearChoresCLS
