-- Prove2me | Theorems.Thm_OAI_Erdos3_relativePatchSliceConclusion_of_budgeted_spatial_buffered_score
-- name    : OAI.Erdos3.relativePatchSliceConclusion_of_budgeted_spatial_buffered_score
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T02:01:18.979827+00:00
-- url     : https://prove2.me/theorems/6fe09ed2-823b-415f-821c-2d42090af813
-- title:
--   A budgeted spatial buffered score gives a relative patch slice conclusion
-- statement:
--   Let $X$ be a finite type with decidable equality and $N : X \to \mathbb N$ with $N_i > 0$ for all $i$; let $q_0 > 0$ be a natural number; let $s, d, E, m, \mathrm{rankBound}$ be natural numbers. Let $w : \mathrm{Fin}\,d \to \mathbb N$ be monotone with $1 \le w_j \le s$; let $P_j \in \mathbb R[X]$ ($j \in \mathrm{Fin}\,d$) have degree at most $w_j$ (`weightedSupportLE 1 (w j)`); let $p : \mathrm{Fin}\,m \to \mathbb N$; let $B$ be a `WeightedParameterPatch (X ⊕ Fin m) (Sum.elim 1 p) s E` (a structure of weights, weighted parameter slots and a `PatchKernel E`, with real value `B.value` and kernel Lipschitz constant `B.kernel.lip`); let $\chi$ be a `PatchKernel m` (a function $\mathbb R^m \to [0,1]$ supported where all $|x_i| \le 1/4$, Lipschitz with constant $\chi.\mathrm{lip}$); let $M : \mathrm{Fin}\,m \times \mathrm{Fin}\,d \to \mathbb Z$ and $K \in \mathbb R_{\ge 0}$ with $\sum_j |M_{ij}| \le K$ for all $i$ and $w_j \le p_i$ whenever $M_{ij} \ne 0$. Let $G : (X \to \mathbb R) \times (X \to \mathbb Z/q_0) \times (\mathrm{Fin}\,m \to \mathbb Z) \times \mathbb R^m \to \mathbb R$ and $\Lambda, L_{\mathrm{lift}}, C \in \mathbb R_{\ge 0}$ with $C \ge 1$, such that $z \mapsto G(z, r, b, y)$ is $\Lambda$-Lipschitz for all $r, b, y$; $y \mapsto G(z, r, b, y)$ is $L_{\mathrm{lift}}$-Lipschitz for all $z, r, b$; $G$ takes values in $[0, C]$; and $G(z, r, \mathrm{recoveredIntegerLift}(M, c, k)) = G(z, r, c)$ for all $z, r, c, k$, where `recoveredIntegerLift M c k` $= c + Mk$. Let $f : (X \to \mathbb Z) \to \mathbb R$ take values in $[0,1]$ on `integerBox N`, and $\mathrm{full} : \prod_i \mathrm{Fin}(N_i) \times (\mathrm{Fin}\,m \to \mathbb Z) \to \mathbb R$. Let $\lambda, \delta, \varepsilon, \mathrm{gain}, L$ be reals with $\lambda, \varepsilon \in [0,1]$, $\delta \ge 0$ and $(1 + \delta)(1 - \varepsilon) \le 1 - \delta$.
--
--   For $u \in \prod_i \mathrm{Fin}(N_i)$ write $Y(u) = M\,(P_j(u))_j \in \mathbb R^m$, $\bar u = (u_i/N_i)_i$ (`BoxProgressionPartition.normalizedPoint u`) and $\hat u = (u_i \bmod q_0)_i$. Assume that for all $u, \beta$,
--   $$(1-\delta)\, G(\bar u, \hat u, \beta, Y(u) - \beta) \le \mathrm{full}(u, \beta) \le (1+\delta)\, G(\bar u, \hat u, \beta, Y(u) - \beta),$$
--   and
--   $$\mathrm{gain} \le \mathop{\mathbb E}_{u \in \prod_i \mathrm{Fin}(N_i)} (f(u) - \lambda) \sum_{\beta : \mathrm{Fin}\,m \to \mathbb Z} \chi(Y(u) - \beta)\, \mathrm{full}(u, \beta)\, B.\mathrm{value}(u, \beta)$$
--   (the sum is a `tsum`; $B.\mathrm{value}(u, \beta)$ is evaluated at the point equal to $u$ on $X$ and $\beta$ on $\mathrm{Fin}\,m$). Assume finally $L \ge 1$; $d, E, |X| \le L$; $K, \Lambda, C, L_{\mathrm{lift}}, \chi.\mathrm{lip}$, `B.kernel.lip` and $q_0$ are at most $e^L$; $e^{-L} \le \mathrm{gain}/(1 + \delta)$; $\exp(\mathrm{spatialPatchExtractionCost}(L)) \le N_i$ for all $i$, where `spatialPatchExtractionCost L` $= 20(L+1)^2$; and $d + E \le \mathrm{rankBound}$.
--
--   Then `RelativePatchSliceConclusion s N f ((1 - ε) λ) rankBound (spatialPatchExtractionCost L)` holds: with $\Gamma = 20(L+1)^2$, there exist $q > 0$, a `ResidueBoxSlice N q` $S'$, a natural number $d'$ and a `PolynomialPatch X s d'` $A'$ such that every side length of $S'$ is at least $e^{-\Gamma} N_i$, $d' \le \mathrm{rankBound}$, `relativePatchComplexity A'` $\le \Gamma$, and $e^{-\Gamma} \le$ `relativePatchSliceScore S' f ((1 - ε) λ) A'`.
--
--   Lean: `OAI.Erdos3.relativePatchSliceConclusion_of_budgeted_spatial_buffered_score` in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1344` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean#L683

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1344

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

theorem relativePatchSliceConclusion_of_budgeted_spatial_buffered_score
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m rankBound : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial X ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (X ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (X → ℝ) → (X → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ Llift C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith Llift (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (full : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    {lam δ ε gain L : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) ≤ full u β)
    (hupper : ∀ u β, full u β ≤ (1 + δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)))
    (hscore : gain ≤ 𝔼 u : (∀ i, Fin (N i)),
      (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin m → ℤ,
        χ.value (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) * full u β *
        B.value (Sum.elim (fun i => ((u i).val : ℝ)) (fun i => (β i : ℝ))))
    (hL : 1 ≤ L) (hd : (d : ℝ) ≤ L) (hE : (E : ℝ) ≤ L)
    (hn : (Fintype.card X : ℝ) ≤ L)
    (hKbudget : (K : ℝ) ≤ Real.exp L) (hΛbudget : (Λ : ℝ) ≤ Real.exp L)
    (hCbudget : (C : ℝ) ≤ Real.exp L) (hLiftbudget : (Llift : ℝ) ≤ Real.exp L)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp L) (hBbudget : (B.kernel.lip : ℝ) ≤ Real.exp L)
    (hq₀budget : (q₀ : ℝ) ≤ Real.exp L)
    (hgainBudget : Real.exp (-L) ≤ gain / (1 + δ))
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost L) ≤ (N i : ℝ))
    (hrank : d + E ≤ rankBound) :
    RelativePatchSliceConclusion s N f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost L) := by
  sorry

end Erdos3
end
end OAI
