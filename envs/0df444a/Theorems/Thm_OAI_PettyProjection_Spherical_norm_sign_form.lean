-- Prove2me | Theorems.Thm_OAI_PettyProjection_Spherical_norm_sign_form
-- name    : OAI.PettyProjection.Spherical.norm_sign_form
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:08:39.585879+00:00
-- url     : https://prove2.me/theorems/3c15da8e-b18e-48ad-9e38-de8f8a98f99d
-- title:
--   Sign-transform lower bound for powers of two norms on the sphere, when the first has no degree-two harmonic part (OpenAI Petty projection)
-- statement:
--   Let $n \ge 2$ (and `[NeZero n]`) and let $\mathbb R^n$ be `Spherical.Space n` (`EuclideanSpace ℝ (Fin n)`) with inner product $\langle\cdot,\cdot\rangle$. Let $S^{n-1}$ be its unit sphere (`Sphere n`) and $\sigma$ the surface measure on it normalized to total mass $1$ (`sigma n`, Mathlib's `volume.toSphere` divided by its total mass). Write $\mathrm{mean}(h) = \int h\,d\sigma$ (`mean`).
--
--   Spaces and operators:
--   - $L^2(\sigma)$ is `Lp ℝ 2 (sigma n)` (`H n`); `toH n` sends a continuous function on $S^{n-1}$ to its class in $L^2(\sigma)$.
--   - $Q$ (`Q n`) is the orthogonal projection of $L^2(\sigma)$ onto the orthogonal complement of the span of the restrictions of the coordinate products $x_i x_j$ (`lowSpace n`).
--   - $\mathcal H_2$ (`harmonicSpace n 2`) is the image in $L^2(\sigma)$ of the homogeneous polynomials $p$ of degree $2$ in $n$ variables with $\sum_i \partial_i^2 p = 0$ (`harmonicPolynomials n 2`), each sent to the class of its restriction to $S^{n-1}$ (`polynomialL2 n`). $P_2$ is the orthogonal projection onto $\mathcal H_2$ (`starProjection`).
--   - For a function $h : \mathbb R^n \to \mathbb R$, its tangential gradient at $x$ is $\nabla h(x) - \bigl(Dh(x)\,x\bigr)\,x$ (`sphereGradient h x`), with Mathlib's gradient `∇ h x` and derivative `fderiv ℝ h x`; both are $0$ where $h$ is not differentiable. For $k \in \mathbb R$ the sign field is $u \mapsto h(u)\,u + k^{-1}\,\mathrm{sphereGradient}\ h\ u$ on $S^{n-1}$ (`signField k h`).
--   - For maps $F, G : S^{n-1} \to \mathbb R^n$, `signedPair F G` is
--   $$\iint_{S^{n-1} \times S^{n-1}} \operatorname{sign}\langle x, y\rangle\,\langle F(x), G(y)\rangle \;d(\sigma \otimes \sigma)(x, y),$$
--   with `Real.sign` (which is $0$ at $0$).
--   - `cosineConstant n` is $2\,\mathrm{mean}\bigl(x \mapsto \max(\langle e_0, x\rangle, 0)\bigr)$, where $e_0$ is the first standard basis vector (`2 * higherKernel 1 (pole n) (fun _ => 1)`).
--
--   Let $f, g$ be seminorms on $\mathbb R^n$ and $k \ge 1$ a natural number. Write $F_k, G_k$ for the restrictions to $S^{n-1}$ of $x \mapsto f(x)^k$ and $x \mapsto g(x)^k$, as continuous functions (`restrictContinuous`, with continuity from the bundle's `seminorm_continuous`). Assume $P_2(F_k) = 0$, i.e. `(harmonicSpace n 2).starProjection (toH n F_k) = 0`. Then
--   $$\mathrm{mean}(f^k)\,\mathrm{mean}(g^k) - c_{n,k}\,\bigl\|Q\,F_k\bigr\|\,\bigl\|Q\,G_k\bigr\| \;\le\; \frac{\mathrm{signedPair}\bigl(\mathrm{signField}\ k\ f^k,\ \mathrm{signField}\ k\ g^k\bigr)}{\mathrm{cosineConstant}\ n},$$
--   where $f^k$ and $g^k$ in the sign fields are the ambient functions $x \mapsto f(x)^k$ and $x \mapsto g(x)^k$, the norms are those of $L^2(\sigma)$, and
--   $$c_{n,k} = \frac{1 + \bigl(\frac{2}{k} + \frac{n-1}{k^2}\bigr)\cdot 4(n+2)}{(n+1)(n+3)}.$$
--
--   Lean: `OAI.PettyProjection.Spherical.norm_sign_form`, OpenAI's theorem of that name (in `lean/OAI/Geometry/ProjectionBodies/NormRigidity.lean`). `Spherical.Space`, `Sphere`, `sigma`, `mean`, `H`, `toH`, `lowSpace`, `Q`, `harmonicPolynomials`, `polynomialL2`, `harmonicSpace`, `restrictContinuous`, `seminorm_continuous`, `sphereGradient`, `signField`, `signedPair`, `higherKernel`, `pole` and `cosineConstant` come from the definitions bundle `OAIQWPP000` of this split.
-- source:
--   OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/NormRigidity.lean (declaration OAI.PettyProjection.Spherical.norm_sign_form)

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

theorem norm_sign_form {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k)
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^k) ((seminorm_continuous n f).pow k))) = 0) :
    mean (fun u : Sphere n => f u^k)*mean (fun u : Sphere n => g u^k) -
      ((1+(2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)*(4*(n+2)))/((n+1)*(n+3)))*
        ‖Q n (toH n (restrictContinuous (fun x => f x^k) ((seminorm_continuous n f).pow k)))‖*
        ‖Q n (toH n (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))‖ ≤
      signedPair (signField (k : ℝ) (fun x => f x^k))
        (signField (k : ℝ) (fun x => g x^k))/cosineConstant n := by
  sorry

end PettyProjection.Spherical
end

end OAI
end
