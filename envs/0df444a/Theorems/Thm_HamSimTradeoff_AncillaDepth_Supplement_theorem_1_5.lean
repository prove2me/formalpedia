-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_theorem_1_5
-- name    : HamSimTradeoff.AncillaDepth.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:50.014804+00:00
-- url     : https://prove2.me/theorems/2d0c6d03-c310-47da-a582-d6eec141e87e
-- title:
--   Theorem 1.5 — balanced-case ancilla-query tradeoff 2^a ≥ L²/(L + 2K_η²(T − 1)) = Ω_η(L²/(T + L)) for ε = η/L, with its three special cases
-- statement:
--   Fix $\eta\in[0,1)$. Consider the fixed repeated-query LCU circuit (1.16) at a positive system dimension $N$, with $L\ge1$, balanced coefficients $\lambda_j=1/L$, and error $\varepsilon=\eta/L$ uniformly for all unitary tuples. Assume $N\ge T(L+1)^2$ and use $K_\eta$ from (1.19). There is $c_\eta>0$, independent of $L,N,T,a$ and the circuit, such that
--   $$2^a\ge\frac{L^2}{L+2K_\eta^2(T-1)},\qquad2^a\ge c_\eta\frac{L^2}{T+L}.$$
--   All three special cases are included:
--   1. For $0\le\alpha<1$ and $C_T>0$ there are $c,D>0$, depending only on $\eta,\alpha,C_T$, such that $T\le C_TL^{1+\alpha}$ implies $2^a\ge cL^{1-\alpha}$ and $a\ge(1-\alpha)\log_2L-D$.
--   2. For $0\le\beta<1$ and $C_a>0$ there is $c>0$, depending only on $\eta,\beta,C_a$, such that $2^a\le C_aL^\beta$ implies $T\ge cL^{2-\beta}$.
--   3. If $\eta=\varepsilon=0$, then $2^a\ge L$ and $a\ge\log_2L$ for every $T$.
--   This is the balanced companion theorem of the effective-support bound. The paper writes Omega_eta and O_eta; Lean chooses each positive constant before every remaining instance parameter.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: O or Omega with uniform constants → positive constants quantified before every parameter over which they are uniform; reason: retains the paper's absolute constants or its indicated dependence on eta or r
--   - encoding: L unitaries with weights 1/L, system dimension N → hypotheses 1 ≤ L and 1 ≤ N inside BalancedInstance; reason: λ_j = 1/L is undefined at L = 0 and U(0) is the trivial empty system; both only exclude degenerate cases
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 8, Theorem 1.5

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Balanced
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem theorem_1_5 : ∀ eta : ℝ, 0 ≤ eta → eta < 1 →
    (∃ c : ℝ, 0 < c ∧ ∀ L N : ℕ, ∀ B : LCUCircuit L, BalancedInstance eta L N B →
      (L:ℝ)^2 / ((L:ℝ)+2*(K eta)^2*((B.T:ℝ)-1)) ≤ (2:ℝ)^B.a ∧
      c*(L:ℝ)^2 / (B.T+L:ℕ) ≤ (2:ℝ)^B.a ∧
      (eta = 0 → L ≤ 2^B.a ∧ Real.log L / Real.log 2 ≤ B.a)) ∧
    (∀ alpha CT : ℝ, 0 ≤ alpha → alpha < 1 → 0 < CT →
      ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ L N : ℕ, ∀ B : LCUCircuit L,
        BalancedInstance eta L N B → (B.T:ℝ) ≤ CT*(L:ℝ)^(1+alpha) →
        c*(L:ℝ)^(1-alpha) ≤ (2:ℝ)^B.a ∧
          (1-alpha)*(Real.log L / Real.log 2)-D ≤ B.a) ∧
    (∀ beta CA : ℝ, 0 ≤ beta → beta < 1 → 0 < CA →
      ∃ c : ℝ, 0 < c ∧ ∀ L N : ℕ, ∀ B : LCUCircuit L,
        BalancedInstance eta L N B → (2:ℝ)^B.a ≤ CA*(L:ℝ)^beta →
        c*(L:ℝ)^(2-beta) ≤ B.T) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
