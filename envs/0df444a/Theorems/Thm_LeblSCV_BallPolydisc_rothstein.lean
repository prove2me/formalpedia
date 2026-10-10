-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_rothstein
-- name    : LeblSCV.BallPolydisc.rothstein
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:22:00.747832+00:00
-- url     : https://prove2.me/theorems/ea6249f4-7a50-47a9-816f-453fc7574eea
-- title:
--   Theorem 1.4.4 (Rothstein 1935) — no proper holomorphic map from the bidisc to the ball
-- statement:
--   Let $\mathbb{D}^2 = \mathbb{D} \times \mathbb{D} = \{ z \in \mathbb{C}^2 : |z_1| < 1,\ |z_2| < 1 \}$ be the unit bidisc and $\mathbb{B}_2 = \{ z \in \mathbb{C}^2 : |z_1|^2 + |z_2|^2 < 1 \}$ the Euclidean unit ball. There exists no proper holomorphic mapping
--   $$f : \mathbb{D}^2 \to \mathbb{B}_2.$$
--
--   Since a biholomorphism is proper, the bidisc and the ball are not biholomorphically equivalent, although they are homeomorphic: in several variables the geometry of the boundary, not only the topology of the domain, decides equivalence. The inequivalence goes back to Poincaré; the first complete proof is H. Cartan's (1931), and the stronger statement about proper maps is Rothstein's (1935).
--
--   **Formalization Note.** $\mathbb{C}^2$ is `Fin 2 → ℂ`. The bidisc is `unitPolydisc 2` and the ball is `unitBall 2`, written with the explicit Euclidean condition (the Mathlib sup-norm unit ball of `Fin 2 → ℂ` is the bidisc itself, for which the identity would be a proper holomorphic map). Holomorphic is `DifferentiableOn ℂ` on the open bidisc, equivalent there to the book's Definition 1.1.2; proper is `IsProperMapOn` (Definition 1.4.3 for the restricted map $\mathbb{D}^2 \to \mathbb{B}_2$).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 33, Theorem 1.4.4

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_unitBall
import Definitions.Def_LeblSCV_BallPolydisc_unitPolydisc
import Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn

namespace LeblSCV.BallPolydisc

/-- Theorem 1.4.4 (Rothstein 1935; Lebl, p. 33). There exists no proper holomorphic mapping of
the unit bidisc `𝔻² ⊆ ℂ²` to the (Euclidean) unit ball `𝔹₂ ⊆ ℂ²`. -/
theorem rothstein :
    ¬ ∃ f : (Fin 2 → ℂ) → (Fin 2 → ℂ),
        DifferentiableOn ℂ f (unitPolydisc 2) ∧
          IsProperMapOn f (unitPolydisc 2) (unitBall 2) := by sorry

end LeblSCV.BallPolydisc
