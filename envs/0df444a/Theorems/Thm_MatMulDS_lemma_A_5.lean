-- Prove2me | Theorems.Thm_MatMulDS_lemma_A_5
-- name    : MatMulDS.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:23.637039+00:00
-- url     : https://prove2.me/theorems/4eac3586-be03-4965-9790-2949c7a51871
-- title:
--   Lemma A.5 — decomposing a query into stored boxes and new products
-- statement:
--   Fix a private map, a compatible weight function, a distribution $\pi$, a threshold $0\le\eta_{\mathrm{pre}}\le\mu$ and an admissible $L$. Let $\Phi_p\Psi_p$ be values at the strings $p$ of products.
--
--   1. For every selected output $o$, the boxes in $B_o$ partition the light products relevant to $o$, so that
--   $$S_o=\sum_{\substack{p\text{ relevant to }o\\\mathrm{ord}_o(p)<t}}\Phi_p\Psi_p+\sum_{b\in B_o}\mathrm{val}(b),$$
--   and the keys of all boxes in $B_o$ lie in $K_{\mathrm{key}}$.
--   2. For $(\kappa,k)\in K_{\mathrm{key}}$ with $k\ge1$, let $o=\rho^{-1}(\kappa_k)$, and for $p\in P_{\mathrm{rel}}(o)$ let $\kappa(p)$ replace $\kappa_k$ by $p$. The box with key $(\kappa,k)$ is the disjoint union of the boxes with keys $(\kappa(p),k-1)$, and all these keys lie in $K_{\mathrm{key}}$. So all stored values can be computed from the products at light strings using at most $P_{\mathrm{base}}$ additions per box.
--
--   This is the correctness of the query of the data structure.
--
--   Differences from the source:
--   - generalization: values $\Phi_p\Psi_p$; $L$ sufficiently large → any function $v$ of the string; every $L\ge1$; reason: the proof uses neither; $v=\Phi\Psi$ and large $L$ give the source claim
--   - encoding: $k$th coordinate, 1-based → the coordinate $\ell$ with $\ell+1=k$, 0-based; the recurrence as an equality of sums; reason: same instances
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma A.5, eq. (A.17), pp.75–76 (PDF pp.77–78)

import Mathlib
import Definitions.Def_MatMulDS_Kkey

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Lemma A.5 (Decomposing a Query), pp.75–76** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256
6c5a1c16…).
(i) For every selected output `o`, the boxes in `B_o` partition the light products relevant to `o`, so that (A.17) holds, and the keys
of all boxes in `B_o` lie in `Kkey`.
(ii) For `(κ, k) ∈ Kkey` with `k ≥ 1`, let `o = ρ⁻¹(κ_k)`, and let `κ(p)` replace `κ_k` by `p`. Then the box with key `(κ, k)` is the
disjoint union of the boxes with keys `(κ(p), k − 1)` for `p ∈ Prel(o)`, and all these keys lie in `Kkey`. In particular, all stored values
can be computed from the products at light strings using at most `P_base` additions per box.

**Formalization Note** The values `Φ_p Ψ_p` are any function `v` of the string: Lemma A.5 does not use what they are, and the case
`v p = Φ_p Ψ_p` is the source's. The `k`th coordinate in the source's 1-based count is `ℓ` with `ℓ + 1 = k` here. -/
theorem lemma_A_5 (F : Type) [Field F] (T : BlockTensor I K J B) (D : IdentityData I K J P)
    (hD : D.Computes T) (ρ : T.Out → P) (hρ : D.IsPrivateMap T ρ) (wt : P → ℝ)
    (hwt : D.IsCompatible T ρ wt) (π : I × J → ℚ) (hπ : IsBlockDistribution T π)
    (hlen : 0 < lenPi T π) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ mu π ρ wt)
    (L : ℕ) (hL : 1 ≤ L) (hadm : IsAdmissible T π L) (v : Str P L → F) :
    -- (i)
    (∀ o : Fin (2 * L) → T.Out, IsSelected π L o →
      (boxesOf D π ρ wt η o : Set (Finset (Str P L))).PairwiseDisjoint id ∧
      (boxesOf D π ρ wt η o).biUnion id = lightRelevant D wt η o ∧
      (∑ p ∈ relevantSet D o, v p =
        ∑ p ∈ heavyRelevant π D ρ wt η o, v p +
          ∑ b ∈ boxesOf D π ρ wt η o, ∑ p ∈ b, v p) ∧
      ∀ p ∈ lightRelevant D wt η o,
        (keyOf π ρ wt η o p, suffixIndex π ρ wt η o p) ∈ Kkey ρ wt η L ∧
        keyBox D ρ (keyOf π ρ wt η o p) (suffixIndex π ρ wt η o p) = boxOf D π ρ wt η o p) ∧
    -- (ii)
    (∀ (κ : Str P L) (k : ℕ), (κ, k) ∈ Kkey ρ wt η L →
      ∀ ℓ : Fin (2 * L), (ℓ : ℕ) + 1 = k → ∀ o' : T.Out, ρ o' = κ ℓ →
        keyBox D ρ κ k = (D.Prel o'.1).biUnion (fun p => keyBox D ρ (Function.update κ ℓ p) (k - 1)) ∧
        ((D.Prel o'.1 : Set P).PairwiseDisjoint fun p => keyBox D ρ (Function.update κ ℓ p) (k - 1)) ∧
        (∀ p ∈ D.Prel o'.1, (Function.update κ ℓ p, k - 1) ∈ Kkey ρ wt η L) ∧
        (∑ q ∈ keyBox D ρ κ k, v q =
          ∑ p ∈ D.Prel o'.1, ∑ q ∈ keyBox D ρ (Function.update κ ℓ p) (k - 1), v q) ∧
        (D.Prel o'.1).card ≤ Fintype.card P) ∧
    (∀ κ : Str P L, keyBox D ρ κ 0 = {κ}) := by sorry

end MatMulDS
