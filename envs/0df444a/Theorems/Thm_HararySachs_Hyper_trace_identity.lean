-- Prove2me | Theorems.Thm_HararySachs_Hyper_trace_identity
-- name    : HararySachs.Hyper.trace_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:40:38.244478+00:00
-- url     : https://prove2.me/theorems/6cafdc25-0139-45f6-9ab5-4efc5bfc4ff3
-- title:
--   Proof of Theorem 14 — resultant coefficient as a Schur expression in traces
-- statement:
--   Let $\phi_d(\mathcal H)$ be the codegree-$d$ coefficient of the resultant characteristic polynomial of a simple $k$-graph. For $1\le d\le n(k-1)^{n-1}$, the identity quoted in the proof of Theorem 14 is
--
--   $$\phi_d(\mathcal H)=P_d\!\left(-\frac{\operatorname{Tr}_1(\mathcal H)}1,\ldots,-\frac{\operatorname{Tr}_d(\mathcal H)}d\right).$$
--
--   This connects the resultant definition of $\phi$ to the combinatorial trace calculation. The identity is cited by Clark and Cooper from earlier work rather than proved in their paper.
--
--   **Formalization Note** A resultant satisfying the common-root criterion, normalization, and irreducibility is supplied. The bound on $d$ keeps the codegree within the paper's characteristic-polynomial expansion.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 12, proof of Theorem 14, first display; citing Cooper and Dutle [4]

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

theorem trace_identity (n k d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (hd1 : 1 ≤ d) (hdt : d ≤ n * (k - 1) ^ (n - 1))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    codegCoeff (k := k) E res d =
      schurP d (fun j => -(Tr (k := k) E j) / (j : ℚ)) := by sorry

end HararySachs.Hyper
