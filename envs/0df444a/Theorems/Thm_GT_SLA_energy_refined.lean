-- Prove2me | Theorems.Thm_GT_SLA_energy_refined
-- name    : GT.SLA.energy_refined
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:31.051387+00:00
-- url     : https://prove2.me/theorems/1dc07f2f-67a7-4bda-b465-fd03d7a93544
-- title:
--   Refining poorly distributed labels increases the energy by at most $2\eta^{C_3}$
-- statement:
--   Let $p$ be prime, $\eta>0$, and let $v$ be a valid structured local approximant (Definition 6.1): a finite probability space of labels $c$, each carrying a base point $n_c$, a frequency set $S_c$, a radius $\rho_c\in(0,1]$, a non-degenerate torus $G_c$, a $1$-Lipschitz function $F_c:G_c\to[-1,1]$ and a locally quadratic map $\Xi_c$ on $n_c+B(S_c,\rho_c)$. Suppose each poorly distributed label $c$ is equipped with refinement data $r_c$ satisfying the conclusions of Proposition 7.1 and the associated numerical conditions, and let $v'$ be the refined approximant obtained by replacing each poorly distributed label by the family of refined labels. Then for every $f:\mathbb{Z}/p\mathbb{Z}\to[0,1]$,
--
--   $$\mathcal{E}_{v'}(f)\le \mathcal{E}_{v}(f)+2\eta^{C_3},$$
--
--   where $\mathcal{E}_v(f)=\mathbb{E}\,|f(\mathbf a)-\mathbf f(\mathbf a)|^2$ is the energy of the random triple $(\mathbf a,\mathbf r,\mathbf f)$ attached to $v$.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 6 (Definition 6.1, proof of Theorem 6.7)

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM Matrix

namespace GT

namespace SLA

theorem energy_refined {p : ℕ} [NeZero p] {v : SLA p} {η : ℝ} (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c))
    (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ((v.refined η rd).triple η).energy f ≤ (v.triple η).energy f + 2 * η ^ C3 := by sorry

end SLA
end GT
