-- Prove2me | Theorems.Thm_GT_bad_dim_thm
-- name    : GT.bad_dim_thm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T10:30:08.162333+00:00
-- url     : https://prove2.me/theorems/29219a60-fb91-4ce1-9e1f-0d08314d75a9
-- title:
--   Theorem 6.7: bad lower bound implies dimension decrement
-- statement:
--   Let $p$ be a prime, $0<\eta\le1/10$ with $p\ge\exp(\eta^{-3C_5})$, and $f:\mathbb{Z}/p\mathbb{Z}\to[0,1]$. Let $v$ be a valid structured local approximant satisfying the bounds (6.4)–(6.7) and suppose the lower bound fails badly:
--
--   $$\Lambda(\mathbf f)\le \big(\mathbb{E}\,\mathbf f(\mathbf a)\big)^4-\eta .$$
--
--   Then there is a valid structured local approximant $v'$ joined to $v$ by an edge (Definition 6.3) such that $d_2(v')\le d_2(v)$, the poorly-distributed quadratic dimension drops, $d_2^{\mathrm{poor}}(v')+1\le d_2^{\mathrm{poor}}(v)$, and the energy increases by at most $\eta^{3C_2}$.
--
--   **Notation.** Throughout, $p$ is a positive integer (usually a prime) and we work in $\mathbb{Z}/p\mathbb{Z}$. For a finite frequency set $S\subseteq\mathbb{Z}/p\mathbb{Z}$ we write $\|h\|_{S^\perp}=\max_{s\in S}\|sh/p\|_{\mathbb{R}/\mathbb{Z}}$ (and $0$ if $S=\emptyset$), $B(S,\rho)=\{x:\|x\|_{S^\perp}\le\rho\}$ for the Bohr set, and $P_{S,\rho}(a)=2\int_{1/2}^{1}\mu_{B(S,t\rho)}(a)\,dt$ for the *regular* probability distribution on $B(S,\rho)$, where $\mu_B$ is the uniform probability measure on $B$. We write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}/\mathbb{Z}$ and $e_p(x)=e(x/p)$ for $x\in\mathbb{Z}/p\mathbb{Z}$. A frequency $\ell$ is *$A$-good* for $T$ if $\|\ell h/p\|_{\mathbb{R}/\mathbb{Z}}\le A\|h\|_{T^\perp}$ for all $h$. All objects are those of the definition bundle `GreenTaoFourCore`.
--
--   **Formalization Note.** This is one node of a machine-checked decomposition of the proof of `Erdos142.green_tao_four` (Green–Tao's bound $r_4(N)\ll N(\log N)^{-c}$). All explicit numerical constants and the precise quantitative side conditions are exactly those of the Lean statement; the notation above is only a reading guide.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Section 6, Theorem 6.7

import Mathlib
import Definitions.Def_GreenTaoFourCore

open Finset KM Matrix

namespace GT

theorem bad_dim_thm {p : ℕ} [NeZero p] (hp : p.Prime) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hpη : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) {f : ZMod p → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {v : SLA p} (hv : v.Valid) (hb : v.Bounds η)
    (hlow : (v.triple η).lamF ≤ (v.triple η).exF ^ 4 - η) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧ v'.d2 ≤ v.d2 ∧ v'.d2p η + 1 ≤ v.d2p η ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f + η ^ (3 * C2) := by sorry

end GT
