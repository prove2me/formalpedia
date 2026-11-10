-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_theorem_3_6_cofactor_induction
-- name    : GinibrePermanent977.Anticoncentration.theorem_3_6_cofactor_induction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:20.541206+00:00
-- url     : https://prove2.me/theorems/4b60f105-72dc-4d61-8f96-1b4b75e358e6
-- title:
--   Theorem 3.6 — Gaussian cofactor induction
-- statement:
--   Throughout, $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$ with $\beta=\dim_{\mathbb R}\mathbb K\in\{1,2,4\}$; a **standard $\mathbb K$-Gaussian** has independent real coordinates $N(0,1/\beta)$, $G_n^{\mathbb K}$ is an $n\times n$ matrix and $B_n$ an $(n-1)\times n$ matrix of i.i.d. standard $\mathbb K$-Gaussian entries, $\operatorname{per}_{\mathbb K}A=\sum_{\sigma}a_{1\sigma(1)}a_{2\sigma(2)}\cdots a_{n\sigma(n)}$ is the row-ordered permanent, and $(C_n^{\mathbb K})_j=\operatorname{per}_{\mathbb K}((B_n)_{-j})$ is the permanental cofactor column ($C_1^{\mathbb K}=(1)$). Let $\gamma_{k,\beta}\sim\mathrm{Gamma}(\beta k/2,2/\beta)$ (shape, scale) be independent, $\Pi_{m,\beta}=\prod_{k=2}^m\gamma_{k,\beta}$ ($\Pi_{0,\beta}=\Pi_{1,\beta}=1$), and for each $m\ge1$ let $g_m^{\mathbb K}$ be a standard $\mathbb K$-Gaussian column in $\mathbb K^m$ independent of the gamma variables.
--
--   For every $n\ge1$:
--
--   1. (15) $\Pi_{n-1,\beta}\,g_n^{\mathbb K}(g_n^{\mathbb K})^*\preceq_{Lt}C_n^{\mathbb K}(C_n^{\mathbb K})^*$;
--   2. (16) $\Pi_{n,\beta}\le_{Lt}\|C_n^{\mathbb K}\|_2^2$;
--   3. (17) for every $z\in\mathbb K^{n+1}$,
--   $$0\le E\,e^{i(z,C_{n+1}^{\mathbb K})_{\mathbb R}}\le E\,e^{i(z,\sqrt{\Pi_{n,\beta}}\,g_{n+1}^{\mathbb K})_{\mathbb R}}.$$
--
--   The gamma products are the inductive benchmark: the permanental cofactor column is dominated in Laplace-transform order by a Gaussian column with the determinant's gamma scale.
--
--   Differences from the source:
--
--   - encoding: $K\in\{\mathbb R,\mathbb C,\mathbb H\}$ → a tag `F : Scalar` with carriers ℝ, ℂ, ℍ[ℝ] and β = 1, 2, 4; reason: Lean convention selecting the three concrete scalar domains; same instances
--   - encoding: 1-based indices $j=1,\dots,n$, $e_1$ → 0-based `Fin n` indices, $e_1$ = `Pi.single 0`; reason: Lean convention; source index j is Lean index j−1
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: $M\preceq_{Lt}N$ for $M=XX^*$, $N=YY^*$, tests $\operatorname{Re}\operatorname{tr}(TM)$, $T\succeq0$ Hermitian → `OuterLaplaceOrder` with $\operatorname{Re}(v^*Tv)$ written as $\sum_i(v_i,(Tv)_i)_{\mathbb R}$, $T$ Hermitian with nonnegative real quadratic form; reason: $\operatorname{Re}\operatorname{tr}(Tvv^*)=\operatorname{Re}(v^*Tv)$ by cyclicity of the real trace; every matrix compared in the paper is a rank-one outer product
--   - encoding: $U\le_{Lt}V$: $Ee^{-sU}\ge Ee^{-sV}$ for $s\ge0$ → published `LaplaceOrder`, quantified over $s>0$; reason: at $s=0$ both sides equal 1 for probability laws; same order
--   - encoding: “$0\le\varphi\le\psi$” for characteristic functions → the order of ℂ (`ComplexOrder`): both sides real and ordered; reason: the source asserts that these values are real; same statement
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.3, p. 10, Theorem 3.6, Eqs. (15)–(17) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Theorem 3.6 (Gaussian cofactor induction), p. 10. Let `K ∈ {ℝ, ℂ, ℍ}` and `β = dim_ℝ K`; for
each `m ≥ 1` let `g_m^K` be a standard `K`-Gaussian column in `K^m`, independent of the gamma
variables. For every `n ≥ 1`:
(15) `Π_{n-1,β} g_n (g_n)^* ⪯_{Lt} C_n^K (C_n^K)^*`;
(16) `Π_{n,β} ≤_{Lt} ‖C_n^K‖₂²`;
(17) for every `z ∈ K^{n+1}`, `0 ≤ E e^{i(z, C_{n+1}^K)_ℝ} ≤ E e^{i(z, √Π_{n,β} g_{n+1}^K)_ℝ}`.
Here `(√Π_{n-1,β} g_n)(√Π_{n-1,β} g_n)^* = Π_{n-1,β} g_n g_n^*`. -/
theorem theorem_3_6_cofactor_induction (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    OuterLaplaceOrder (benchLaw F n) (ginibre F (n - 1) n) benchVec perCofactor ∧
      StochasticOrders.LaplaceTransform.LaplaceOrder (gammaVec F n) (ginibre F (n - 1) n)
        gammaPi (fun B => norm2 (perCofactor B) ^ 2) ∧
      ∀ z : Fin (n + 1) → F.K,
        0 ≤ charFunK (ginibre F n (n + 1)) (perCofactor (n := n + 1)) z ∧
          charFunK (ginibre F n (n + 1)) (perCofactor (n := n + 1)) z ≤
            charFunK (benchLaw F (n + 1)) benchVec z := by sorry

end GinibrePermanent977.Anticoncentration
