-- Prove2me | Theorems.Thm_MatMulDS_lemma_6_1
-- name    : MatMulDS.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:57.947791+00:00
-- url     : https://prove2.me/theorems/7e11b592-4fec-4c83-a34d-1da0d0890132
-- title:
--   Lemma 6.1 — enlargement lengthens the central output without new products
-- statement:
--   Consider a bijective approximate bilinear identity for a block tensor, with $r$ products, $n_A$ left variables and $n_B$ right variables, which is $\varepsilon$-homogeneous and has a central block with central output $w_0$ of length $d$. Let $d^*=r-(n_A-d)-(n_B-d)$. Then there is an identity with $r$ products, $n_A-d+d^*$ left variables and $n_B-d+d^*$ right variables such that:
--
--   1. it has the same outputs, and computes the same bilinear forms at all of them except $w_0$;
--   2. it is $\varepsilon$-homogeneous and has a central block with central output $w_0$, now of length $d^*$;
--   3. it computes a block tensor with blocks of the same outputs, and every output has the same relevant products.
--
--   In particular, the new identity is bijective with the same private map, and every strict compatible weight function remains so. This raises the score whenever the given identity has $n_A+n_B<r+d$.
--
--   Differences from the source:
--   - reading: the relevant products of an output "appear with the same coefficient" (p.28) → that coefficient is a power $\varepsilon^{e(o)}$; reason: p.66 states this form and "we assume this property throughout"; the proof keeps it, $C^\prime=\varepsilon^{2K-h}C$
--   - encoding: new variables with new middle indices → middle indices $K\oplus\mathrm{Fin}\,n$, with the new ones on the right; reason: the construction of p.41; same instances
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma 6.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_MatMulDS_IsEnlargement

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Lemma 6.1 (Enlargement), p.40** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256
6c5a1c16…). A bijective identity for a block tensor which is ε-homogeneous and has a central block has an enlargement
(properties (a), (b), (c), packaged in `IsEnlargement`). In particular, the new identity is bijective, with the same
private map as the given identity, and every strict weight function compatible with this private map remains so. -/
theorem lemma_6_1 (T : BlockTensor I K J B) (D : IdentityData I K J P) (β₀ : B) (w₀ : I × J)
    (hD : D.Computes T) (hbij : IsBijective T P) (hhom : D.IsHomogeneous T)
    (hcen : D.IsCentralBlock T β₀ w₀) :
    ∃ (n : ℕ) (T' : BlockTensor I (K ⊕ Fin n) J B) (D' : IdentityData I (K ⊕ Fin n) J P),
      IsEnlargement T D β₀ w₀ T' D' ∧
      IsBijective T' P ∧
      ∀ (ρ : T.Out → P) (ρ' : T'.Out → P), (∀ o o', o.1 = o'.1 → ρ' o' = ρ o) →
        D.IsPrivateMap T ρ →
        D'.IsPrivateMap T' ρ' ∧
        ∀ wt : P → ℝ, D.IsCompatible T ρ wt → D.IsStrict T ρ wt →
          D'.IsCompatible T' ρ' wt ∧ D'.IsStrict T' ρ' wt := by sorry

end MatMulDS
