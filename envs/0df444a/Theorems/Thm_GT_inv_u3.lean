-- Prove2me | Theorems.Thm_GT_inv_u3
-- name    : GT.inv_u3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:52.624008+00:00
-- url     : https://prove2.me/theorems/76c859c3-e374-4e9b-9e66-c159f7f0fbb1
-- title:
--   Theorem 8.1: the local inverse $U^3$ theorem
-- statement:
--   Let $p$ be prime, $S\subseteq\mathbb{Z}/p\mathbb{Z}$ with a non-zero element and $|S|\le s$, let $0<\eta\le2^{-30}$, $0<\rho_0\le1$, $0<\theta\le\theta(s,\eta)$ and $p\ge P(s,\eta,\theta,\rho_0)$. Let $f:\mathbb{Z}/p\mathbb{Z}\to\mathbb{C}$ with $|f|\le1$ and suppose the local $U^3$ average at scales $\rho_0,\theta\rho_0,\theta^2\rho_0$ is large:
--
--   $$\eta\le\Big|\mathbb{E}_{h_i,h_i'\sim P_{S,\theta^i\rho_0}}\ \prod_{\omega\in\{0,1\}^3}\mathcal{C}^{|\omega|}f\big(h_0^{\omega_0}+h_1^{\omega_1}+h_2^{\omega_2}\big)\Big|.$$
--
--   Then there are $1\le k\le\exp((s+J+1)^3)$, a frequency set $S'\supseteq S$ with $|S'|\le|S|+J$ where $J=\eta^{-2^{24}}$, a locally quadratic phase $\phi$ on $B(S',2\theta^{T}\rho_0)$ with $T=T(\eta)$, and $\beta:\mathbb{Z}/p\mathbb{Z}\to\mathbb{Z}/p\mathbb{Z}$, such that
--
--   $$\eta^{2^{20}}\le\sum_n P_{S,\rho_0}(n)\,\Big|\sum_m P_{S',\theta^T\rho_0}(m)\,f(n+km)\,e\big(-\phi(m)-\beta(n)m/p\big)\Big|.$$
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 8, Theorem 8.1

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM ComplexConjugate

namespace GT

theorem inv_u3 {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)}
    (hS : ∃ s ∈ S, s ≠ 0)
    {s : ℕ} (hs : S.card ≤ s) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 ^ 30)
    {ρ0 θ : ℝ} (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1) (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η)
    (hpl : u3P s η θ ρ0 ≤ p) (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hU : η ≤ ‖u3avg S ρ0 (θ * ρ0) (θ ^ 2 * ρ0) f‖) :
    ∃ (k : ℕ) (S' : Finset (ZMod p)) (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
      1 ≤ k ∧ (k : ℝ) ≤ u3k s η ∧ S ⊆ S' ∧ (S'.card : ℝ) ≤ S.card + u3J η ∧
      LocQuad (sBohr S' 0 (2 * (θ ^ u3T η * ρ0))) φ ∧
      u3κ η ≤ ∑ n, regP S ρ0 n * ‖∑ m, (regP S' (θ ^ u3T η * ρ0) m : ℂ) *
        (f (n + k * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ := by sorry

end GT
