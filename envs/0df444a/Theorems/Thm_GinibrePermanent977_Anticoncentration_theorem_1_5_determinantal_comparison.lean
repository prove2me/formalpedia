-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_theorem_1_5_determinantal_comparison
-- name    : GinibrePermanent977.Anticoncentration.theorem_1_5_determinantal_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:29.89995+00:00
-- url     : https://prove2.me/theorems/90f90571-cc85-4e60-9143-f464775bc0a9
-- title:
--   Theorem 1.5 — determinantal cofactor comparison
-- statement:
--   Let $\mathbb F\in\{\mathbb R,\mathbb C\}$, let $B_n$ be an $(n-1)\times n$ standard $\mathbb F$-Gaussian matrix with permanental and signed determinantal cofactor columns $(C_n^{\mathrm{per}})_j=\operatorname{per}((B_n)_{-j})$, $(C_n^{\det})_j=(-1)^{j-1}\det((B_n)_{-j})$ ($C_1^{\mathrm{per}}=C_1^{\det}=(1)$), and let $G_n$ be a standard $\mathbb F$-Ginibre matrix. For every $n\ge1$:
--
--   1. (4) $C_n^{\det}(C_n^{\det})^*\preceq_{Lt}C_n^{\mathrm{per}}(C_n^{\mathrm{per}})^*$;
--   2. (5) $|\det G_n|^2\le_{Lt}|\operatorname{per}G_n|^2$;
--   3. (6) for every $z\in\mathbb F^{n+1}$,
--   $$0\le E\,e^{i\operatorname{Re}\langle z,C_{n+1}^{\mathrm{per}}\rangle}\le E\,e^{i\operatorname{Re}\langle z,C_{n+1}^{\det}\rangle}.$$
--
--   The squared Gaussian permanent dominates the squared determinant in Laplace-transform order; this is the comparison from which the density bound for $\mathbb F\in\{\mathbb R,\mathbb C\}$ follows.
--
--   Differences from the source:
--
--   - encoding: $\mathbb F\in\{\mathbb R,\mathbb C\}$ → a tag `F : Scalar` with `F ≠ quaternion`; reason: Lean convention; same two fields
--   - encoding: 1-based indices $j=1,\dots,n$, $e_1$ → 0-based `Fin n` indices, $e_1$ = `Pi.single 0`; reason: Lean convention; source index j is Lean index j−1
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: $M\preceq_{Lt}N$ for $M=XX^*$, $N=YY^*$, tests $\operatorname{Re}\operatorname{tr}(TM)$, $T\succeq0$ Hermitian → `OuterLaplaceOrder` with $\operatorname{Re}(v^*Tv)$ written as $\sum_i(v_i,(Tv)_i)_{\mathbb R}$, $T$ Hermitian with nonnegative real quadratic form; reason: $\operatorname{Re}\operatorname{tr}(Tvv^*)=\operatorname{Re}(v^*Tv)$ by cyclicity of the real trace; every matrix compared in the paper is a rank-one outer product
--   - encoding: $U\le_{Lt}V$: $Ee^{-sU}\ge Ee^{-sV}$ for $s\ge0$ → published `LaplaceOrder`, quantified over $s>0$; reason: at $s=0$ both sides equal 1 for probability laws; same order
--   - encoding: $\det$ over $\mathbb R,\mathbb C$ → `cdetK` (Leibniz sum with row-ordered products); reason: equals the determinant over a commutative field
--   - encoding: “$0\le\varphi\le\psi$” for characteristic functions → the order of ℂ (`ComplexOrder`): both sides real and ordered; reason: the source asserts that these values are real; same statement
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §1.1, p. 3, Theorem 1.5, Eqs. (4)–(6); Definitions 1.3–1.4, p. 3 (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Theorem 1.5 (Determinantal cofactor comparison), p. 3. For each `F ∈ {ℝ, ℂ}` and every
`n ≥ 1`:
(4) `C_n^{det}(C_n^{det})^* ⪯_{Lt} C_n^{per}(C_n^{per})^*`;
(5) `|det G_n|² ≤_{Lt} |per G_n|²`;
(6) for every `z ∈ F^{n+1}`, `0 ≤ E e^{i Re⟨z, C_{n+1}^{per}⟩} ≤ E e^{i Re⟨z, C_{n+1}^{det}⟩}`. -/
theorem theorem_1_5_determinantal_comparison (F : Scalar) (hF : F ≠ Scalar.quaternion)
    (n : ℕ) (hn : 1 ≤ n) :
    OuterLaplaceOrder (ginibre F (n - 1) n) (ginibre F (n - 1) n) detCofactor perCofactor ∧
      StochasticOrders.LaplaceTransform.LaplaceOrder (ginibre F n n) (ginibre F n n)
        (fun G => ‖cdetK G‖ ^ 2) (fun G => ‖perK G‖ ^ 2) ∧
      ∀ z : Fin (n + 1) → F.K,
        0 ≤ charFunK (ginibre F n (n + 1)) (perCofactor (n := n + 1)) z ∧
          charFunK (ginibre F n (n + 1)) (perCofactor (n := n + 1)) z ≤
            charFunK (ginibre F n (n + 1)) (detCofactor (n := n + 1)) z := by sorry

end GinibrePermanent977.Anticoncentration
