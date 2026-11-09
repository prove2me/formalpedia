-- Prove2me | Theorems.Thm_NoisyOWMPC_corollary_A_8
-- name    : NoisyOWMPC.corollary_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:22.128246+00:00
-- url     : https://prove2.me/theorems/90b44fe0-0b8f-485c-926e-8b56b2c60dd7
-- title:
--   Corollary A.8 — list-recoverable expanders
-- statement:
--   Fix constants $c\ge0$ and $0<\gamma\le1$. There is a family of layered graphs $G(M,\ell,G)$ with $M$ layers, left vertices $\{0,1\}^\kappa$ and right vertices $[M]\times H$, computed (neighbors and recovery) by deterministic polynomial-time machines, and constants $K_1,K_2>0$, $e$, $M_0$, such that for every $M\ge M_0$ with $M+1$ a power of two and all integers $\ell,G$ with
--   $$1\le\ell\le M^c,\qquad M^\gamma\le G\le M,$$
--   the graph is $(M\ell,G,L_{\mathrm{out}})$-list-recoverable with $L_{\mathrm{out}}\le M^e$, $|H|\le M^e$, and $K_1\sqrt G\log_2M\le\kappa\le K_2\sqrt G\log_2M$.
--
--   This is the instantiation of the Guruswami–Umans–Vadhan expanders [GUV09] used by all three recovery algorithms.
--
--   Differences from the source:
--   - reading: efficiently constructible; recovery algorithm deterministic, polynomial time in M → neighbor maps and recovery computed by deterministic polynomial-time machines on (1^M, 1^ℓ, 1^G, …); reason: the paper's notion of an explicit expander
--   - encoding: κ = Θ(√G log M), |H| = M^{O(1)}, L_out = M^{O(1)} → explicit constants K₁, K₂, e; reason: definition of Θ and O
--   - encoding: right vertices [M] × H → labels H = [h]; reason: a finite label set up to renaming
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Corollary A.8, p.48 (Theorem 3.7, p.17, [GUV09])

import Mathlib
import Definitions.Def_NoisyOWMPC_IsA8Family

namespace NoisyOWMPC

/-- **Corollary A.8 (A sufficient condition for list-recoverable expanders)** (Ishai, Lu, Zafar,
STOC 2027 submission (manuscript sha256 3a9569fa…), Corollary A.8, p.48, an instantiation of
[GUV09] cited as Theorem 3.7, p.17): "Fix constants `c ≥ 0` and `0 < γ ≤ 1`. Let `q = M + 1` be a
power of two, and let integer parameters `ℓ, G` satisfy `1 ≤ ℓ ≤ M^c`, `M^γ ≤ G ≤ M`. For all
sufficiently large `M`, there is an efficiently constructible layered `(Mℓ, G, L_out)`-list-
recoverable expander `G` with left vertices `{0,1}^κ`, right vertices `[M] × H`, and one neighbor in
each layer, where `κ = Θ(√G log M)`, `|H| = M^{O(1)}`, `L_out = M^{O(1)}`. Its recovery algorithm
is deterministic and runs in time polynomial in `M` for the fixed constants `c, γ`."

**Formalization Note** "Efficiently constructible" is a family `Gr M ℓ G` whose neighbor maps and
recovery algorithm are computed by deterministic polynomial-time machines (`IsA8Family`). -/
theorem corollary_A_8 (c : ℝ) (hc : 0 ≤ c) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr c γ := by sorry

end NoisyOWMPC
