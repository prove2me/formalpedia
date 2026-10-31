-- Prove2me | Theorems.Thm_GhostPenalty_eq_25
-- name    : GhostPenalty.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:19.315319+00:00
-- url     : https://prove2.me/theorems/9e168ac7-6789-4429-b906-31f6a79dd539
-- title:
--   (25) — one-step estimate $W(x+\gamma d;\varepsilon)-W(x;\varepsilon)\le\gamma\nabla f^Td-\frac\gamma\varepsilon\theta+\frac{\gamma^2}2(L_{\nabla f}+\frac{\max_iL_{\nabla g_i}}\varepsilon)\|d\|^2$
-- statement:
--   Throughout, $K\subseteq\mathbb R^n$ is nonempty, closed and convex, $f$ and $g=(g_1,\dots,g_m)$ are $C^{1,1}$ on an open set containing $K$, $\lambda\in(0,1)$ and $0<\rho<\beta$ are the parameters of $\kappa$, and the surrogates $\tilde f,\tilde g$ satisfy Assumption A with modulus $c>0$.
--
--   Let $d$ be the solution map of $(\mathrm P_x)$ on $K$, $x\in K$, $\gamma\in(0,1]$, $\varepsilon>0$, and let $L_{\nabla f}$ and $L_{\nabla g_i}$ be Lipschitz constants of $\nabla f$ and $\nabla g_i$ on the segment $[x,\,x+\gamma d(x)]$. Then, with $d=d(x)$,
--   $$W(x+\gamma d;\varepsilon)-W(x;\varepsilon)\le\gamma\nabla f(x)^Td-\frac{\gamma}{\varepsilon}\theta(x)+\frac{\gamma^2}{2}\Big(L_{\nabla f}+\frac{\max_iL_{\nabla g_i}}{\varepsilon}\Big)\|d\|^2. \tag{25}$$
--   This is the descent estimate for the ghost penalty that drives the convergence proof.
--
--   Differences from the source:
--   - generalization: A1 and A5: strong convexity of f̃(•;x) and convexity of g̃_i(•;x) on the open set O_d → strong convexity and convexity on the box βBⁿ∞ ⊆ O_d; reason: O_d need not be convex; every use of A1 and A5 is at points of βBⁿ∞, so the hypothesis is weaker and the statement specializes to the source's
--   - encoding: d(x) = argmin of (Pₓ), the unique solution → a map d with hypothesis IsSubproblemSolutionMap (d(x) ∈ X̃(x) minimizes f̃(•;x) for every x ∈ K); reason: the minimizer exists and is unique under Assumption A (milestone subproblem_well_posed), so d is the source's map on K
--   - generalization: L_∇f, L_∇g_i the Lipschitz moduli of ∇f, ∇g_i on the bounded set containing all iterates; at an iterate x^ν with stepsize γ^ν → Lipschitz constants on the segment [x, x + γ d(x)] only; at every x ∈ K and γ ∈ (0,1]; reason: the descent lemma only evaluates the gradients on that segment, which lies in the convex hull of consecutive iterates, so constants valid on the paper's set are valid here; the derivation uses only x ∈ K and γ ∈ (0,1]
--   - encoding: max_i{L_∇g_i} → ⨆ i, L i (0 when m = 0); reason: maximum over a finite index set
--   - generalization: g : ℝⁿ → ℝᵐ with constraint indices i ∈ {1,…,m}, at least one constraint (max_i over a nonempty index set) → any m : ℕ, including m = 0, with max_i{g_i(x)+} = 0 and every constraint clause empty; reason: at m ≥ 1 the statement is the source's; m = 0 only adds the problem without constraints
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Theorem 1, proof, (25), p.15

import Mathlib
import Definitions.Def_GhostPenalty_StandingAssumptions
import Definitions.Def_GhostPenalty_AssumptionA
import Definitions.Def_GhostPenalty_IsSubproblemSolutionMap
import Definitions.Def_GhostPenalty_theta
import Definitions.Def_GhostPenalty_W
open scoped RealInnerProductSpace NNReal

namespace GhostPenalty

/-- **Inequality (25): one-step decrease estimate for the ghost penalty `W`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Theorem 1, proof, (25), p.15: "`W(x^{ν+1};ε) − W(x^ν;ε) = … ≤ γ^ν∇f(x^ν)ᵀd(x^ν) −
(γ^ν/ε) θ(x^ν) + ((γ^ν)²/2)(L_{∇f} + max_i{L_{∇g_i}}/ε)‖d(x^ν)‖², (25) where (a) follows applying the
descent lemma to `f` and `g_i` for every `i = 1,...,m`, with `L_{∇f}` and `L_{∇g_i}` being the
Lipschitz moduli of `∇f` and `∇g_i` on the bounded set containing all iterates; (b) holds for any
positive `γ^ν ≤ 1`".

For `x ∈ K`, `γ ∈ (0,1]`, `ε > 0`, and Lipschitz constants `L_f`, `L_i` of `∇f`, `∇g_i` on the
segment `[x, x + γd(x)]`:
`W(x + γd(x); ε) − W(x; ε) ≤ γ⟨∇f(x), d(x)⟩ − (γ/ε)θ(x) + (γ²/2)(L_f + max_i L_i / ε)‖d(x)‖²`.

The standing hypotheses are the blanket assumptions on (P) (`StandingAssumptions`: `K`
nonempty closed convex, `f`, `g` C^{1,1} on an open set containing `K`), the parameters
`λ ∈ (0,1)` (`lam`), `ρ ∈ (0,β)` of (8), and Assumption A for the surrogates `f̃ = ft`,
`g̃ = gt` with neighbourhoods `O_d = Od`, `O_x = Ox` and modulus `c`. `d` solves (Pₓ) at every `x ∈ K`. The Lipschitz moduli are taken on the segment from
`x` to `x + γd(x)` (the only points the descent lemma evaluates), which lies inside any convex set
containing the iterates `x^ν` and `x^{ν+1}`; constants valid on the paper's larger set are valid
here. `max_i L_i` is `⨆ i`, which is `0` when `m = 0`. -/
theorem eq_25 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hP : StandingAssumptions K f g)
    (β lam ρ c : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hρ : ρ ∈ Set.Ioo 0 β)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (hA : AssumptionA f g K β ft gt Od Ox c)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hd : IsSubproblemSolutionMap ft g gt K lam ρ β d) :
    ∀ x ∈ K, ∀ γ ∈ Set.Ioc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ (Lf : ℝ≥0) (L : Fin m → ℝ≥0),
      LipschitzOnWith Lf (gradient f) (segment ℝ x (x + γ • d x)) →
      (∀ i, LipschitzOnWith (L i) (gradient (g i)) (segment ℝ x (x + γ • d x))) →
      W f g ε (x + γ • d x) - W f g ε x ≤
        γ * ⟪gradient f x, d x⟫ - γ / ε * theta g gt K lam ρ x +
          γ ^ 2 / 2 * ((Lf : ℝ) + (⨆ i, (L i : ℝ)) / ε) * ‖d x‖ ^ 2 := by sorry

end GhostPenalty
