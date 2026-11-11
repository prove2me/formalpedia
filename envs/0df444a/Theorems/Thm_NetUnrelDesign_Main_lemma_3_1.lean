-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_3_1
-- name    : NetUnrelDesign.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:58.599351+00:00
-- url     : https://prove2.me/theorems/1f039d8b-e22f-430b-8b6c-10c1b99c4a6e
-- title:
--   Lemma 3.1 — pivotal investment: Σ w_e d_e ≤ u(log(1/u) + C log²(2n)) and Pr{T_x > a | K ≥ 2} ≤ 5e^{−a/S}
-- statement:
--   There is one absolute constant $C>0$ such that the following holds for every network $(G,q^0)$ (connected, $n\ge2$, $0<q^0_e\le1$) and every design $x\ge0$. Write $w_e=-\log q^0_e+x_e$, $d_e=\mathbb E_xb_e(\Pi)$ and $T_x(\Pi)=\sum_ex_eb_e(\Pi)$. Then
--   $$\sum_ew_ed_e\le u(x)\bigl[\log(1/u(x))+C\log^2(2n)\bigr].\tag{3.2}$$
--   For every $\eta>0$ with $\eta\le u(x)\le1/32$, put $S=(\log(2/\eta)+C\log^2(2n))/\log2$ with the same $C$. Then, for every real $a$,
--   $$\Pr_x\{T_x>a\mid K\ge2\}\le5e^{-a/S}.\tag{3.3}$$
--
--   Differences from the source:
--
--   - generalization: §3 standing data: a box X_W, W ≥ 1, a known 0 < η ≤ u*_W, the design in X_W → any η > 0 and any design x ≥ 0 of the network (no budget data A, b, no box); reason: (3.2)–(3.3) are properties of the random graph (App. C proves them for arbitrary weights with x_e ≤ w_e); the source's case is the special case x ∈ X_W, η ≤ u*_W
--   - encoding: G is the paper's network (standing assumption of §1: connected, n ≥ 2) → hypotheses 2 ≤ n and IsConnectedGraph ends; reason: the paper's graph always satisfies them; no instance of the source is excluded
--   - encoding: Pr_x{T_x > a | K ≥ 2} → Pr(K ≥ 2 and T_x > a) / u(x); reason: u(x) = Pr(K ≥ 2) ≥ η > 0
--   - encoding: C an absolute constant, the same in (3.2) and S → ∃ C > 0 quantified before all networks, designs, η and a; reason: uniformity made explicit
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 3.1, p. 9 (PDF 10); proof App. C.3, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators

namespace NetUnrelDesign.Main

/-- **Lemma 3.1 (Pivotal investment).** There is one absolute constant `C > 0` such that, for every
network `(G, q⁰)` (connected, `n ≥ 2`, `0 < q⁰_e ≤ 1`) and every design `x ≥ 0`, with
`w_e = −log q⁰_e + x_e` and `d_e = E_x b_e(Π)`:
(3.2) `Σ_e w_e d_e ≤ u(x)[log(1/u(x)) + C log²(2n)]`; and, for every `η > 0` with
`η ≤ u(x) ≤ 1/32`, writing `T_x(Π) = Σ_e x_e b_e(Π)` and `S = (log(2/η) + C log²(2n))/log 2` with
the same `C`, (3.3) `Pr_x{T_x > a | K ≥ 2} ≤ 5 e^{−a/S}` for every real `a`.
Sun 2026, p. 9 (PDF 10). -/
theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n m : ℕ} (ends : Ends n m) (q0 : Fin m → ℝ), NetStanding ends q0 →
        ∀ x : Fin m → ℝ, (∀ e, 0 ≤ x e) →
          (∑ e, weightAt q0 x e * pivotalMean ends (failProbAt q0 x) e ≤
              risk ends q0 x * (Real.log (1 / risk ends q0 x) + C * Real.log (2 * n) ^ 2)) ∧
          ∀ η : ℝ, 0 < η → η ≤ risk ends q0 x → risk ends q0 x ≤ 1 / 32 → ∀ a : ℝ,
            prob (failProbAt q0 x)
                (fun F => 2 ≤ numComponents ends F ∧
                  a < pivotalInvestment ends x (partitionOf ends F)) / risk ends q0 x ≤
              5 * Real.exp (-a / tailScale n η C) := by sorry

end NetUnrelDesign.Main
