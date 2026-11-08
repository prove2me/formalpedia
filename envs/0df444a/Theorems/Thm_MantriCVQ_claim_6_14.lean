-- Prove2me | Theorems.Thm_MantriCVQ_claim_6_14
-- name    : MantriCVQ.claim_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:22.578992+00:00
-- url     : https://prove2.me/theorems/ad47062d-18e8-49b2-a326-247e59a9a79b
-- title:
--   Claim 6.14 — a decision tree from small certificates
-- statement:
--   For every CNF $H$ of width at most $W$ on $\mathbb F_2^K$ and every integer $q\ge1$ there is a decision tree $T$ of depth at most $Wq$ such that $T(z)\le H(z)$ for every $z$, and $T(z)=1$ whenever $H(z)=1$ and $\mathrm C_1(H,z)\le q$. This truncates the standard construction of decision trees from certificates to certificates of size at most $q$. It is what turns the tail bound of Theorem 6.9 into the switching theorem.
--
--   Differences from the source:
--   - encoding: the tree is determined by H and q → an existential for each fixed H and q; reason: a function of H and q is the same as this quantifier order
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.14, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_MantriCVQ_C1
import Definitions.Def_MantriCVQ_CNF
import Definitions.Def_MantriCVQ_DT
import Definitions.Def_MantriCVQ_listWidth

open SamplingAC0

namespace MantriCVQ

/-- **Claim 6.14** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.14, p. 32 (PDF p. 34)): for every CNF `H` of width at most `W` on `F₂^K` and
every integer `q ≥ 1` there is a decision tree `T` of depth at most `Wq` such that `T(z) ≤ H(z)` for every
`z`, and `T(z) = 1` whenever `H(z) = 1` and `C₁(H, z) ≤ q`.

**Formalization Note** "The tree is determined by `H` and `q`" is the order of quantifiers of the
existential, for fixed `H` and `q`. -/
theorem claim_6_14 {K W : ℕ} (H : CNF (Fin K)) (hH : listWidth H ≤ W) (q : ℕ) (hq : 1 ≤ q) :
    ∃ T : DT K, T.depth ≤ W * q ∧
      (∀ z : Fin K → Bool, T.eval z = true → CNF.eval H z = true) ∧
      ∀ z : Fin K → Bool, CNF.eval H z = true → C1 (CNF.eval H) z ≤ q → T.eval z = true := by sorry

end MantriCVQ
