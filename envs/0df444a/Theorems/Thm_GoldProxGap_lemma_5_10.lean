-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_10
-- name    : GoldProxGap.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:25:04.530564+00:00
-- url     : https://prove2.me/theorems/63148608-5a1f-421e-8a72-c974ae2320fc
-- title:
--   Lemma 5.10 — level sets of a quadratic function: exactly $2^{2t}$ labels make $\psi$ vanish on $V$, and $\psi+\kappa$ is one at exactly $T$ points
-- statement:
--   **Lemma 5.10 (Level sets of a quadratic function).** In the setting of (5.2), let $A$ be an alternating binary matrix of rank $2t$ with $1\le t\le d/2$, let $V$ be its polar radical, and put $T=N/2-N/2^{t+1}$. Exactly $2^{2t}$ labels $\omega\in\hat D$ make $\psi$ vanish on $V$. For each of them $\psi$ is constant on every coset of $V$, and exactly one $\kappa\in\mathbb F_2$ makes $\psi+\kappa$ take the value one at $T$ points of $D$ and the value zero at the other $N-T$.
--
--   These level sets $\{\psi+\kappa=1\}$ are the agreement sets of the Gold construction, of size slightly below $N/2$.
--
--   **Formalization Note** A label is given by its linear function $\varphi$; the labels counted are $\{\mathrm{label}(\varphi):\psi\ \text{vanishes on}\ V\}$, a set of field elements. $V$ is the polar radical of $\psi_A$.
--
--   Differences from the source:
--   - encoding: a basis ω₁, …, ω_d of the label space D̂ → a coordinate basis φs of the linear functions D → F₂ with ω_i = label(φs i); reason: by Lemma 5.5(2) the label map is an F₂-linear bijection, so this is the same data
--   - encoding: labels ω ∈ D̂ (with ψ built from ℓ_ω) → labels of linear functions φ (with ψ built from ℓ_φ), counted as the image set {label φ}; reason: every label is the label of a linear function
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.10, p.41

import Mathlib
import Definitions.Def_GoldProxGap_quadPoly

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.10 (Level sets of a quadratic function)**, p.41. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let A have rank 2t with 1 ≤ t ≤ d/2, let V be its polar radical, and put T = N/2 − N/2^{t+1}.
Exactly 2^{2t} labels ω ∈ D̂ make ψ vanish on V. For each of them, ψ is constant on every coset of
V, and exactly one κ ∈ F₂ makes ψ + κ take the value one at T points of D and the value zero at
the other N − T."

**Formalization Note.** Setting of (5.2) (p.38): `A` alternating binary, a coordinate basis `φs`
with `ω_i = label D (φs i)`; `ψ = psi φs A φ` for the linear function `φ` of the label `ω`. `V` is
the polar radical of `ψ_A = psi φs A 0` (the same for every `ω`). The labels counted are
`{label D φ : ψ vanishes on V}`, a subset of `B`. -/
theorem lemma_5_10 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) (d : ℕ)
    (hD : Nat.card D = 2 ^ d) (φs : Fin d → (D →+ ZMod 2)) (hφs : IsCoordBasis D φs)
    (t : ℕ) (ht : 1 ≤ t) (htd : 2 * t ≤ d)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hA : IsAltBin A) (hrank : A.rank = 2 * t) :
    let V := polarRadical (psi φs A 0)
    let T := 2 ^ d / 2 - 2 ^ d / 2 ^ (t + 1)
    (label D '' {φ : D →+ ZMod 2 | ∀ v ∈ V, psi φs A φ v = 0}).ncard = 2 ^ (2 * t) ∧
    ∀ φ : D →+ ZMod 2, (∀ v ∈ V, psi φs A φ v = 0) →
      (∀ x : D, ∀ v ∈ V, psi φs A φ (x + v) = psi φs A φ x) ∧
      ∃! κ : ZMod 2,
        (Finset.univ.filter (fun x : D => psi φs A φ x + κ = 1)).card = T ∧
        (Finset.univ.filter (fun x : D => psi φs A φ x + κ = 0)).card = 2 ^ d - T := by sorry

end GoldProxGap
