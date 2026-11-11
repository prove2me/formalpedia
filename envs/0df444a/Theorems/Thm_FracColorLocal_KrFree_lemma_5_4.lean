-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_5_4
-- name    : FracColorLocal.KrFree.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:24.41021+00:00
-- url     : https://prove2.me/theorems/02b47e31-1d17-4707-bd5b-f76a8e3fd233
-- title:
--   Lemma 5.4 (existence statement) — a witness of (5.1)–(5.2) yields w′ ≥ 0 with ‖w′ − w‖₁ ≤ J_p(w) and U(w′) − U(w) > 2^{4p}p·b(A) − ηJ_p(w)
-- statement:
--   Fix an integer $r\ge4$. Let $G$ be a finite $K_r$-free graph, let $u,w,\theta>0$ be vertex weights and fix $\eta\ge0$. Suppose $\theta_vw(v)\ge2r\xi_v$ for every $v$ and $\|\zeta\|_\infty\le\eta$, where $\xi_v=\xi_{u(v)}(w(v))$ and $\zeta_v=U'_{u(v)}(w(v))-2w(N(v))$. If $A,B\subseteq V$, an integer $p\ge1$ and $\rho$ satisfy (5.1) and (5.2),
--
--   $$w(A),w(B)\le\rho2^p,\quad b(B)\le\rho^22^{2p},\quad e_w(A,B)>24\big(p\,b(A)+\rho^22^{-p}\big),$$
--
--   then there is a nonnegative vertex weight $w'$, zero on a nonempty set of vertices and at least $w$ at every other vertex, such that
--
--   $$\|w'-w\|_1\le J_p(w),\qquad U(w')-U(w)\ >\ 2^{4p}\,p\,b(A)-\eta J_p(w),$$
--
--   with $J_p(w)=(1+2^{(12r-14)p})w(V(G))$ and $U=U_{G,u}$. At a maximizer ($\eta=0$) this rules out alternative (ii) of Lemma 5.1.
--
--   Differences from the source:
--   - reading: "A, B, p, ρ satisfy (5.1) and (5.2)" → $A,B\subseteq V$, an integer $p\ge1$ and a real $\rho$ with the four inequalities; reason: $p$ is the integer $p\ge1$ of Lemma 5.1(ii) (the proof uses $p\ge1$); the lemma places no condition on $\rho$, and (5.1)–(5.2) force $\rho>0$.
--   - reading: the lemma's last sentence (for rational $w,\theta$, $w'$ can be constructed deterministically in polynomial time) → not stated; reason: it belongs to the algorithmic results (Theorem 1.9, Corollary 1.10), which this mission does not formalize; the existence statement is stated with every clause.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 21 (PDF 22), §5.3, (5.4) and Lemma 5.4 (existence statement)

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Potential
import Definitions.Def_FracColorLocal_KrFree_Dichotomy

namespace FracColorLocal.KrFree

/-- Lemma 5.4 (existence statement): a witness `(A, B, p, ρ)` of (5.1)–(5.2) yields a nonnegative
`w'`, zero on a nonempty set and at least `w` elsewhere, with `‖w' - w‖₁ ≤ J_p(w)` and
`U(w') - U(w) > 2^{4p} p b(A) - η J_p(w)`. -/
theorem lemma_5_4 {V : Type*} [Fintype V] (r : ℕ) (hr : 4 ≤ r) (G : SimpleGraph V)
    (hG : G.CliqueFree r) (u w θ : V → ℝ) (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v)
    (hθ : ∀ v, 0 < θ v) (η : ℝ) (hη : 0 ≤ η)
    (hθξ : ∀ v, 2 * r * xiV u w v ≤ θ v * w v)
    (hζ : ∀ v, |zetaV G u w v| ≤ η)
    (A B : Finset V) (p : ℕ) (hp : 1 ≤ p) (ρ : ℝ) (hwit : IsWitness G w θ A B p ρ) :
    ∃ w' : V → ℝ, (∀ v, 0 ≤ w' v) ∧
      (∃ Z : Finset V, Z.Nonempty ∧ (∀ v ∈ Z, w' v = 0) ∧ ∀ v ∉ Z, w v ≤ w' v) ∧
      ∑ v, |w' v - w v| ≤ Jp r p w ∧
      (2 : ℝ) ^ (4 * p) * p * bMass θ w A - η * Jp r p w < potential G u w' - potential G u w := by sorry

end FracColorLocal.KrFree
