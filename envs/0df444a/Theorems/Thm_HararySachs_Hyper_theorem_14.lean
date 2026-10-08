-- Prove2me | Theorems.Thm_HararySachs_Hyper_theorem_14
-- name    : HararySachs.Hyper.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:28.172679+00:00
-- url     : https://prove2.me/theorems/31efac57-aae6-4d91-8dad-ace0cd4419e6
-- title:
--   Theorem 14, labeled form — the hypergraph Harary–Sachs coefficient formula
-- statement:
--   Let $\mathcal H$ be a simple $k$-graph on $[n]$, with $k\ge2$ and $1\le d\le n(k-1)^{n-1}$. For each $m$, sum over ordered $m$-tuples $(S_1,\ldots,S_m)$ of labeled connected Veblen infragraphs of $\mathcal H$ whose total number of edges is $d$. Then
--
--   $$\phi_d(\mathcal H)=\sum_{m=1}^d\frac{\bigl(-(k-1)^n\bigr)^m}{m!}\sum_{(S_1,\ldots,S_m)}\prod_{i=1}^m C_{S_i}.$$
--
--   This labeled identity is the class-weighted Harary–Sachs formula of Theorem 14 before collecting isomorphic components. It expresses a coefficient of the resultant characteristic polynomial using finite rooted-hypergraph counts.
--
--   **Formalization Note** The chosen form is the alternative explicitly permitted by the chunk brief. Its equivalence to the printed class-weighted sum uses Definition 11 and Lemma 12, which are not formalized here. The resultant is supplied with Theorem 3's three properties; $n\ge1$ and the codegree range are stated explicitly.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, pp. 12–13, Theorem 14 and its proof, with Lemma 12 on p. 10

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Veblen

namespace HararySachs.Hyper
open Classical

theorem theorem_14 (n k d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (hd1 : 1 ≤ d) (hdt : d ≤ n * (k - 1) ^ (n - 1))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    codegCoeff (k := k) E res d =
      ∑ m ∈ Finset.Icc 1 d,
        (-((k : ℚ) - 1) ^ n) ^ m / (Nat.factorial m : ℚ) *
          ∑ T ∈ (tuples E d m).filter (fun T =>
              (∑ i, (T i).card) = d ∧
              ∀ i, IsVeblen (T i) k ∧ IsConnected (T i)),
            ∏ i, assocCoeff (T i) := by sorry

end HararySachs.Hyper
