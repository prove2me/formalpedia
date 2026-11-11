-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_proposition_B_2
-- name    : GrothendieckPD.Digits.proposition_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:46.683295+00:00
-- url     : https://prove2.me/theorems/b9739bd2-4553-4576-b7e5-9c622abe5097
-- title:
--   Proposition B.2 (one-variable criterion): $v_n(q)\le v_*$ for all $n\ge1$, hence Theorem 4.1
-- statement:
--   Let $q$ be the sequence of Eq. (4.1), and let $v_n(q)=\sup_{f,g}|\langle f,Qg\rangle|$ over measurable $f,g:\mathbb R^n\to[-1,1]$ (Eq. B.1). Suppose finitely many closed intervals $I=[a,b]$ cover $[0,1]$, each carrying dimension-independent parameters $(w^{(7)},w^{(9)},H_p,K_p,\ell_h,\ell_k,t,c_h,c_k,C)$ (rational, $H_p,K_p$ symmetric) that satisfy (B.7), (B.8),
--   $$F(M)\le C\ \text{ for every feasible }M\quad(B.11),\qquad C+\max_{x\in\partial I}\Phi(x)\le v_*=\frac{1000}{1773}-10^{-9}\quad(B.12),$$
--   where $\partial I=\{a,b\}$ and $B_N,\Gamma_m,\alpha,\beta,F,\Phi$ are the objects of §B.1. Then
--   $$v_n(q)\le v_*\quad\text{for every }n\ge1,$$
--   hence Theorem 4.1: $v_\infty(q)\le1000/1773$ (with $v_\infty$ the Boolean value of §2.1) and $K_G\ge1.773$.
--
--   The criterion reduces the infinite-dimensional bound on $\mathrm{OPT}(Q)$ to finitely many matrix inequalities and one 44-dimensional quadratic bound per interval.
--
--   Differences from the source:
--   - reading: v_n(q) in Appendix B → the (B.1) value gameValueB1 (measurable f, g : ℝⁿ → [−1, 1], absolute value); reason: Appendix B defines v_n by (B.1) on p. 19
--   - reading: 'hence Theorem 4.1' → the conclusions gameValueInf q ≤ 1000/1773 (the §2.1 Boolean value) and 1773/1000 ≤ K_G; reason: Theorem 4.1 (p. 11) states exactly these two clauses
--   - encoding: a finite family of closed intervals I covering [0, 1], ∂I its endpoints → a Fintype-indexed family [a_i, b_i], a_i ≤ b_i, with [0, 1] ⊆ ⋃ [a_i, b_i]; max over ∂I = max(Φ(a_i), Φ(b_i)); reason: same objects
--   - encoding: w^{(N)} ∈ ℚ^{(N−1)/2} indexed j = 1, …, (N−1)/2; σ ∈ {−1, 1}^N → Fin-indexed vectors with entry j equal to w_{j+1}; σ as Boolean vectors; reason: relabelling only
--   - encoding: K_G = sup_{m,n} sup_{A} SDP(A)/OPT(A) (Eq. 1.1) → K_G = inf{K : SDP(A) ≤ K·OPT(A) for all real matrices A} (published GrothendieckConstant.grothendieckConst), with unit vectors in ℝ^d for arbitrary d; reason: same value: the ratio is undefined only at A = 0, where both sides vanish; OPT(A) > 0 for A ≠ 0; the admissible set is nonempty (Grothendieck's inequality) and bounded below; unit vectors in any dimension give the same SDP value as in ℝ^{m+n}
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Proposition B.2, p. 20; setting and Eq. (B.3)–(B.10), p. 19

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_OneVariable

namespace GrothendieckPD.Digits

/-- Proposition B.2 (one-variable criterion, p. 20; setting p. 19). Let finitely many closed
intervals `[a_i, b_i]` cover `[0, 1]`, each with dimension-independent rational parameters
satisfying (B.7), (B.8), `F(M) ≤ C` for every feasible `M` (B.11), and
`C + max(Φ(a_i), Φ(b_i)) ≤ v_* = 1000/1773 - 10^{-9}` (B.12). Then the (B.1) value satisfies
`v_n(q) ≤ v_*` for every `n ≥ 1`, for `q` of Eq. (4.1); hence Theorem 4.1:
`v_∞(q) ≤ 1000/1773` and `K_G ≥ 1.773`. -/
theorem proposition_B_2 {ι : Type} [Fintype ι] (a b : ι → ℝ) (P : ι → CertParams)
    (hab : ∀ i, a i ≤ b i)
    (hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, Set.Icc (a i) (b i))
    (hsymm : ∀ i, ParamsSymm (P i))
    (hB7 : ∀ i, CondB7 (P i))
    (hB8 : ∀ i, CondB8 (P i))
    (hB11 : ∀ i, ∀ M : Fin 44 → ℝ, Feasible M → Fval (P i) M ≤ (P i).C)
    (hB12 : ∀ i, ((P i).C : ℝ) + max (Phi (P i) (a i)) (Phi (P i) (b i)) ≤ vStar) :
    (∀ n : ℕ, 1 ≤ n → gameValueB1 n qCert ≤ vStar) ∧
      gameValueInf qCert ≤ 1000 / 1773 ∧
      (1773 / 1000 : ℝ) ≤ GrothendieckConstant.grothendieckConst := by sorry

end GrothendieckPD.Digits
