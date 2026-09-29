-- Prove2me | Theorems.Thm_GT_loc_to_glob
-- name    : GT.loc_to_glob
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:31:03.729018+00:00
-- url     : https://prove2.me/theorems/4e27bbab-33ac-4184-a492-c0bb38f793a1
-- title:
--   Corollary 4.11: locally quadratic-free phases are close to linear phases
-- statement:
--   Let $N\ge1$, $S\subseteq\mathbb{Z}/N\mathbb{Z}$ non-empty, $\rho>0$, $A\ge1$, $n_0\in\mathbb{Z}/N\mathbb{Z}$ and $\phi:\mathbb{Z}/N\mathbb{Z}\to\mathbb{R}/\mathbb{Z}$. Suppose that for all $h,k\in B(S,\rho/2)$
--
--   $$\big\|\phi(n_0+h+k)-\phi(n_0+h)-\phi(n_0+k)+\phi(n_0)\big\|\le\frac{A\|h\|_{S^\perp}\|k\|_{S^\perp}}{\rho^2}.$$
--
--   Then there is $\xi\in\mathbb{Z}/N\mathbb{Z}$ such that for all $h\in B(S,\rho)$
--
--   $$\Big\|\phi(n_0+h)-\phi(n_0)-\frac{\xi h}{N}\Big\|\le 10^9\sqrt A\,|S|^4\,\frac{\|h\|_{S^\perp}}{\rho}.$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 4, Corollary 4.11

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset ComplexConjugate KM

namespace GT

theorem loc_to_glob {N : ℕ} [NeZero N] {S : Finset (ZMod N)} (hS : S.Nonempty) {ρ A : ℝ} (hρ : 0 < ρ) (hA : 1 ≤ A)
    (φ : ZMod N → UnitAddCircle) (n0 : ZMod N)
    (hφ : ∀ h k, h ∈ bohr S (ρ / 2) → k ∈ bohr S (ρ / 2) →
      ‖φ (n0 + h + k) - φ (n0 + h) - φ (n0 + k) + φ n0‖ ≤ A * snorm S h * snorm S k / ρ ^ 2) :
    ∃ ξ : ZMod N, ∀ h ∈ bohr S ρ,
      ‖φ (n0 + h) - φ n0 - ZMod.toAddCircle (ξ * h)‖ ≤
        10 ^ 9 * √A * (S.card : ℝ) ^ 4 * snorm S h / ρ := by sorry

end GT
