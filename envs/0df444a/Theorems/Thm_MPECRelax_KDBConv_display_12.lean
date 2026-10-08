-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_display_12
-- name    : MPECRelax.KDBConv.display_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:15.805784+00:00
-- url     : https://prove2.me/theorems/2999e51c-24e7-440b-894d-f1478104f575
-- title:
--   Proof of Theorem 3.5, p. 15, (12) — eventually the multiplier supports lie in I_00 ∪ I_0+ resp. I_00 ∪ I_+0
-- statement:
--   Let the data of the MPEC (1) be continuously differentiable, let $\{t_k\}\downarrow 0$ with $t_k>0$, and for every $k$ let $x^k$ be feasible for $R^{KDB}(t_k)$ with KKT multipliers $\lambda^k,\alpha^k,\beta^k,\gamma^k,\mu^k$. Put $\eta^{G,k}_i:=-\gamma^k_i(H_i(x^k)-t_k)$ and $\eta^{H,k}_i:=-\gamma^k_i(G_i(x^k)-t_k)$, and suppose $x^k\to x^*$. Then for all $k$ sufficiently large
--   $$\begin{aligned}
--   \operatorname{supp}(\lambda^k)&\subseteq I_g(x^k)\subseteq I_g,\\
--   \operatorname{supp}(\alpha^k)&\subseteq I_G(x^k,t_k)\subseteq I_{00}\cup I_{0+},\\
--   \operatorname{supp}(\beta^k)&\subseteq I_H(x^k,t_k)\subseteq I_{00}\cup I_{+0},\\
--   \operatorname{supp}(\eta^{G,k})&\subseteq I^{0*}_\Phi(x^k,t_k)\subseteq I_{00}\cup I_{0+},\\
--   \operatorname{supp}(\eta^{H,k})&\subseteq I^{*0}_\Phi(x^k,t_k)\subseteq I_{00}\cup I_{+0},
--   \end{aligned}\tag{12}$$
--   where $I_g$, $I_{00}$, $I_{0+}$, $I_{+0}$ are the index sets at $x^*$ and $I_G$, $I_H$, $I^{0*}_\Phi$, $I^{*0}_\Phi$ are the index sets (10) of the relaxed program.
--
--   These inclusions localize the active multipliers of the relaxed programs to the constraints that are active for the tightened program TNLP$(x^*)$, which is what makes the constraint qualification at $x^*$ applicable.
--
--   **Formalization Note** The first row, for the standard inequality constraints $g$, is not printed: the paper skips the standard constraints in this proof, and the row is their part of (12). "$\{t_k\}\downarrow0$" is encoded as $t_k>0$, $t$ nonincreasing and $t_k\to 0$. "For all $k$ sufficiently large" is `∀ᶠ k in atTop`.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 15, proof of Theorem 3.5, display (12)

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- Proof of Theorem 3.5, p. 15, display (12). Let `t_k ↓ 0`, let `x^k` be feasible for
R^KDB(t_k) with KKT multipliers `(Λ^k, mu^k)`, and let `x^k → xs`. Then for all `k`
sufficiently large the supports of the multipliers `α^k`, `β^k`, `η^{G,k}`, `η^{H,k}`
lie in the index sets (10) at `(x^k, t_k)`, which in turn lie in `I_00 ∪ I_0+`
resp. `I_00 ∪ I_+0` at `xs`. The first row (for the standard inequality constraints:
`supp(λ^k) ⊆ I_g(x^k) ⊆ I_g`) is the part of (12) the paper skips. -/
theorem display_12 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → MPECRelax.ScholtesConv.E n) (xs : MPECRelax.ScholtesConv.E n) (hx : Tendsto x atTop (𝓝 xs))
    (Λ : ℕ → Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l → ℝ) (mu : ℕ → Fin p → ℝ)
    (hfeas : ∀ k, (P.RKDB (t k)).Feasible (x k))
    (hKKT : ∀ k, (P.RKDB (t k)).KKTMult (x k) (Λ k) (mu k)) :
    ∀ᶠ k in atTop,
      (Function.support (MPEC.kdbLam (Λ k)) ⊆ P.Ig (x k) ∧ P.Ig (x k) ⊆ P.Ig xs) ∧
      (Function.support (MPEC.kdbAlpha (Λ k)) ⊆ P.IGt (x k) (t k) ∧
        P.IGt (x k) (t k) ⊆ P.I00 xs ∪ P.I0p xs) ∧
      (Function.support (MPEC.kdbBeta (Λ k)) ⊆ P.IHt (x k) (t k) ∧
        P.IHt (x k) (t k) ⊆ P.I00 xs ∪ P.Ip0 xs) ∧
      (Function.support (P.etaG (x k) (t k) (MPEC.kdbGamma (Λ k))) ⊆ P.IPhi0s (x k) (t k) ∧
        P.IPhi0s (x k) (t k) ⊆ P.I00 xs ∪ P.I0p xs) ∧
      (Function.support (P.etaH (x k) (t k) (MPEC.kdbGamma (Λ k))) ⊆ P.IPhis0 (x k) (t k) ∧
        P.IPhis0 (x k) (t k) ⊆ P.I00 xs ∪ P.Ip0 xs) := by sorry

end MPECRelax.KDBConv
