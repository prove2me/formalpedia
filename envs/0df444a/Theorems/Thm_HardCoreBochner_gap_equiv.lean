-- Prove2me | Theorems.Thm_HardCoreBochner_gap_equiv
-- name    : HardCoreBochner.gap_equiv
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:25.706213+00:00
-- url     : https://prove2.me/theorems/296a7fa7-223b-410b-966b-165d74dec114
-- title:
--   §2 — the equivalent spectral gap $\inf_f\langle Lf,Lf\rangle_\mu/\langle f,-Lf\rangle_\mu$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$, with generator $L$. The spectral gap (2) can equivalently be written
--   $$\gamma(L)=\inf_f\frac{\langle Lf,Lf\rangle_\mu}{\langle f,-Lf\rangle_\mu}.$$
--   Stated as inequalities: for every real $\delta$,
--   $$\Big(\forall f:\ \delta\,\langle f,-Lf\rangle_\mu\le\langle Lf,Lf\rangle_\mu\Big)\iff\Big(\forall f:\ \delta\,\mathrm{Var}_\mu(f)\le\langle f,-Lf\rangle_\mu\Big).$$
--   Each infimum is the largest $\delta$ for which its inequality holds for all $f$, so the two infima coincide. This lets §2 prove the spectral gap by bounding $\langle Lf,Lf\rangle_\mu$.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
--   - encoding: equality of the infima γ(L) = inf_f ⟨f, −Lf⟩_µ/Var_µ(f) = inf_f ⟨Lf, Lf⟩_µ/⟨f, −Lf⟩_µ → for every real δ: (∀ f, δ ⟨f, −Lf⟩_µ ≤ ⟨Lf, Lf⟩_µ) ↔ (∀ f, δ Var_µ(f) ≤ ⟨f, −Lf⟩_µ); reason: two infima of ratios are equal exactly when the same δ's lie below them; the inequality form avoids 0/0 and empty infima
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §2, p.7 (PDF p.7)

import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip

namespace HardCoreBochner

open scoped BigOperators

/-- **The equivalent definition of the spectral gap.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §2, p.7: "γ(L) = inf_f ⟨Lf, Lf⟩µ /
⟨f, −Lf⟩µ. The equivalence to (2) follows from self-adjointness of L".

In Poincaré form: for every real `δ`, the inequality `δ ⟨f, −Lf⟩_µ ≤ ⟨Lf, Lf⟩_µ` holds for all `f`
if and only if `δ Var_µ(f) ≤ ⟨f, −Lf⟩_µ` holds for all `f`. Each infimum is the largest `δ` for which
its inequality holds, so the two infima are equal.

**Formalization Note** "γ ≥ δ" for an infimum of ratios is written as the inequality it means,
with no ratio, so constant functions (`0/0`) and an empty infimum (`X = {∅}`) cause no junk value. -/
theorem gap_equiv {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ : IsDownClosedLaw μ) (δ : ℝ) :
    (∀ f : (V → Bool) → ℝ, δ * ip μ f (fun σ => -gen μ f σ) ≤ ip μ (gen μ f) (gen μ f)) ↔
      ∀ f : (V → Bool) → ℝ, δ * var μ f ≤ ip μ f (fun σ => -gen μ f σ) := by sorry

end HardCoreBochner
