-- Prove2me | Theorems.Thm_LiftSAParity_sa_duality
-- name    : LiftSAParity.sa_duality
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:34.018327+00:00
-- url     : https://prove2.me/theorems/958b34c5-7f17-42f0-8c0e-b71baae3832b
-- title:
--   Sherali–Adams duality [FKP19] — $d$-local distribution iff no degree-$d$ refutation
-- statement:
--   Let $\varphi$ be a CNF formula on $n$ variables and $d\in\mathbb N$. Then
--   $$\varphi\text{ has a }d\text{-local distribution}\iff\varphi\text{ has no Sherali–Adams refutation of degree at most }d .$$
--
--   The paper quotes this from [FKP19] to pass from the hypothesis of Theorem 1.1 (no low-degree refutation) to that of Theorem 4.1 (a local distribution).
--
--   **Formalization Note** The degree of a refutation is measured term by term: $\deg p+\deg q_p\le d$ and $\deg h_\alpha\le d$ (footnote 1, p.4).
--
--   Differences from the source:
--   - reading: degree of a refutation: the maximum degree of a monomial in it, clauses in product form, total degree of each term (footnote 1) → deg p + deg q_p ≤ d for every axiom p with q_p ≠ 0, and deg h_α ≤ d; reason: the footnote's term-by-term degree; it is the reading under which the duality holds in both directions
--   - generalization: variables x_1, …, x_n with n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 both sides say that φ does not contain the empty clause; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4, citing [FKP19] (footnote 1: Def. 2.20, Thm. 2.17, Lemma 2.21, Thm. 2.37 there)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_SARefutation
import Definitions.Def_LiftSAParity_HasSADegreeAtMost

namespace LiftSAParity

/-- **Sherali–Adams duality [FKP19]** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §1.1, p.4): "By Sherali–Adams duality, φ has a d-local
distribution if and only if it has no Sherali–Adams refutation of degree at most d [FKP19]."

**Formalization Note** The degree of a refutation is the strict measure `HasSADegreeAtMost`
(`deg p + deg q_p ≤ d` for every used axiom `p`, and `deg h_α ≤ d`), footnote 1, p.4. -/
theorem sa_duality (n : ℕ) (φ : CNF (Fin n)) (d : ℕ) :
    (∃ D : (I : Finset (Fin n)) → (I → Bool) → ℝ, IsLocalDist φ d D) ↔
      ¬ ∃ π : SARefutation φ, HasSADegreeAtMost π d := by sorry

end LiftSAParity
