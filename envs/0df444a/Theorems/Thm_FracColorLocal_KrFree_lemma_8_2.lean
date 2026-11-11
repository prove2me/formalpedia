-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_8_2
-- name    : FracColorLocal.KrFree.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:10.93947+00:00
-- url     : https://prove2.me/theorems/35b098ba-6868-4992-ab86-1c2b33fdf1f2
-- title:
--   Lemma 8.2 — entropy chain −log t ≤ H_0 ≤ … ≤ H_t ≤ C_ent log t and a common j < t with E_τ‖K^j_x(v,·) − K^j_x(z,·)‖_TV ≤ 2√((C_ent+1) log t/t)
-- statement:
--   Let $t\ge32$ be an integer and $F$ a finite graph with positive vertex weights $w$ and parameters $\theta$ in the situation of §8.1 after edge deletion: $F$ has no isolated vertices, $\Lambda_x=w(N(x))\le R_t\theta_x$ at every vertex and $C_{xv}=w(N(x)\cap N(v))\ge\max(\theta_x,\theta_v)/t$ on every edge (8.4), and $0<D<T$ for $D=D_\theta(F)$, $T=T_F(w)$ (8.3). If both tests (8.10) and (8.11) hold at every vertex of $F$, then
--
--   $$-\log t\le H_0\le H_1\le\cdots\le H_t\le C_{\mathrm{ent}}\log t, \tag{8.17}$$
--
--   and some common index $0\le j<t$ satisfies
--
--   $$\mathbb E_{(x,v,z)\sim\tau}\big\|K^j_x(v,\cdot)-K^j_x(z,\cdot)\big\|_{\mathrm{TV}}\ \le\ 2\sqrt{(C_{\mathrm{ent}}+1)\log t/t}. \tag{8.18}$$
--
--   Here $H_j=\mathbb E_{(x,v)\sim\nu}H_{s_x}(K^j_x(v,\cdot))$, $K^j_x=P_xQ_x^j$ are the neighbourhood-walk kernels, and $\nu,\tau$ are the edge and triangle laws of §8.2. The common walk length $j$ is where the label coupling of §9 splits vertices with little triangle loss.
--
--   Differences from the source:
--   - generalization: "the graph $F$ obtained after edge deletion" (from a current graph with $\Lambda_v/\theta_v\le2^t$ and $T_{\mathrm{in}}>2D_{\mathrm{in}}$) → every graph $F$ with no isolated vertices satisfying (8.4) and $0<D<T$; reason: these are the properties §8.1 establishes for $F$ ((8.3) gives $T>D_{\mathrm{in}}\ge D>0$), so the procedure's output is one such graph.
--   - encoding: expectations under $\nu$ and $\tau$ → finite sums against the laws `edgeLaw`, `triangleLaw`; walk matrices as $V\times V$ matrices vanishing outside $N(x)$; reason: same values.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 37 (PDF 38), Lemma 8.2, (8.17), (8.18); context §8.1–§8.4, pp. 33–37 (PDF 34–38)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Constants
import Definitions.Def_FracColorLocal_KrFree_Dichotomy
import Definitions.Def_FracColorLocal_KrFree_Walk

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Lemma 8.2, for every graph `F` with the properties §8.1 establishes for the graph obtained
after edge deletion: no isolated vertices, `Λ_x ≤ R_t θ_x` and `C_xv ≥ max(θ_x, θ_v)/t` (8.4),
`0 < D < T` (8.3), and tests (8.10), (8.11) at every vertex. -/
theorem lemma_8_2 {V : Type*} [Fintype V] (F : SimpleGraph V) (w θ : V → ℝ) (t : ℕ)
    (ht : 32 ≤ t) (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    (hiso : ∀ v, ∃ y, F.Adj v y)
    (hΛ : ∀ x, neighborMass F w x ≤ (Rt t : ℝ) * θ x)
    (hC : ∀ x v, F.Adj x v → max (θ x) (θ v) / t ≤ commonMass F w x v)
    (hD : 0 < dTheta F w θ) (hDT : dTheta F w θ < triangleMass F w)
    (h810 : ∀ v, Test810 F w θ t v) (h811 : ∀ v, Test811 F w θ t v) :
    (-Real.log t ≤ avgEntropy F w θ 0 ∧
      (∀ j < t, avgEntropy F w θ j ≤ avgEntropy F w θ (j + 1)) ∧
      avgEntropy F w θ t ≤ (Cent : ℝ) * Real.log t) ∧
    ∃ j < t, avgTriangleTV F w j ≤ 2 * Real.sqrt (((Cent : ℝ) + 1) * Real.log t / t) := by sorry

end FracColorLocal.KrFree
