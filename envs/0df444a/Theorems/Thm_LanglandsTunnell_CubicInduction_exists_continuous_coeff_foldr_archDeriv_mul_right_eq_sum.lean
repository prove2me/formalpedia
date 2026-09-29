-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
-- name    : LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/0605ebf9-5e90-5ab7-9284-8ee4f40296b9
-- title:
--   Derivative words of a right translate on GL₃(A_ℚ)
-- statement:
--   Work on $G = \mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$, i.e. on `AdelicGL 3 (𝓞 ℚ) ℚ`, the group of invertible $3\times 3$ matrices over `AdeleRing (𝓞 ℚ) ℚ`. For indices $i,j \in \{0,1,2\}$ and $\varphi : G \to \mathbb{C}$, `WhittakerBlock.archDeriv i j φ` is the function sending $g$ to the derivative at $s=0$ of $s \mapsto \varphi\bigl(g \cdot \mathrm{archRealLift3}(I + s E_{ij})\bigr)$, where for a real $3\times 3$ matrix $e$ the element $\mathrm{archRealLift3}(e)$ of $G$ is the unit attached to the adelic matrix `archRealMat3 e` when that matrix is invertible and $1$ otherwise. The predicate [`WhittakerBlock.IsArchSmooth3 φ`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) says that for every $g \in G$ the map $e \mapsto \varphi(g \cdot \mathrm{archRealLift3}(e))$ on real $3\times 3$ matrices is $C^\infty$ on the locus $\{e : \det e \neq 0\}$. The assertion: given a list $w$ of pairs of indices, of length $n$, there is a family of complex numbers $\mathrm{coeff}(k,f)$, indexed by $k \in G$ and by functions $f : \{0,\dots,n-1\} \to \{0,1,2\}^2$, such that (i) for each such $f$ the map $k \mapsto \mathrm{coeff}(k,f)$ is continuous on $G$, and (ii) for every $\varphi$ satisfying `IsArchSmooth3` and all $k, g \in G$, applying the derivative operators listed by $w$ (folded from the right, so the last entry of $w$ acts first) to the right translate $x \mapsto \varphi(xk)$ and evaluating at $g$ gives $\sum_f \mathrm{coeff}(k,f)\,(\partial_f \varphi)(gk)$, where $\partial_f$ is the same fold applied to the list of values of $f$ and the sum runs over all $9^n$ such $f$. The coefficients depend only on $w$ and $k$, not on $\varphi$ or $g$.
--
--   This is the statement that the algebra of archimedean directional derivative operators on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ is stable under right translation, with expansion coefficients that vary continuously in the translating element. It is used in the bounds on Whittaker functions and on their ray orders, in particular in the finiteness and invariance estimates for the archimedean centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
    (w : List (Fin 3 × Fin 3)) :
    ∃ coeff : AdelicGL 3 (𝓞 ℚ) ℚ → (Fin w.length → Fin 3 × Fin 3) → ℂ,
      (∀ f : Fin w.length → Fin 3 × Fin 3, Continuous fun k => coeff k f) ∧
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ k g : AdelicGL 3 (𝓞 ℚ) ℚ,
        List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (fun x => φ (x * k)) w g =
          ∑ f : Fin w.length → Fin 3 × Fin 3,
            coeff k f * List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (g * k) := by sorry
