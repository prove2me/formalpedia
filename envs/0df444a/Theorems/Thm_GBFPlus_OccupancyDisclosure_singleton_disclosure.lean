-- Prove2me | Theorems.Thm_GBFPlus_OccupancyDisclosure_singleton_disclosure
-- name    : GBFPlus.OccupancyDisclosure.singleton_disclosure
-- status  : Proved
-- author  : @queelius
-- created : 2026-10-23T18:33:04.32098+00:00
-- url     : https://prove2.me/theorems/f3d117cf-b439-470a-923d-c6a6cb61a486
-- title:
--   Proposition 1: singleton occupancy reveals the adjacent-domain identifier
-- statement:
--   For every valid configuration and every honest history with exactly one successful row $r$, XORing all publicly occupied words and taking the final $\ell$ bits yields the adjacent-domain identifier in $r$. This holds for every selected position set, prefix, empty pivot and free-share realization allowed by the construction, including occupied zero shares. The equation $\operatorname{successful}(es)=[r]$ names the unique successful row and is equivalent to the successful count being one with that row identified. The recovery function uses only the snapshot and public widths. Interpreting this identity as disclosure presupposes the source's genuine public occupancy, authentic honestly generated snapshot and permitted singleton release; it does not establish deployment frequency or the identifier-only privacy game.
-- source:
--   Alexander Richard Towell, Adjacent-Domain Disclosure from Public Occupancy in GBFPlus, archival preprint v1.0.0, 20 October 2026, Section 2, DOI 10.5281/zenodo.23497466. Original analyzed protocol: Qin, Zhou, Dai, Sun and Qiang, Entropy 28 (2026), 947, DOI 10.3390/e28090947, Algorithm 4 and Sections 5.1–5.2. The source note is CC-BY-4.0; this new Lean formalization retains attribution and is prepared for the platform public-contribution terms. Section 2, Proposition 1 (Singleton disclosure), Eq.(2), with the preceding construction and Section 1 environmental premises.

import Mathlib
import Definitions.Def_GBFPlus_OccupancyDisclosure

namespace GBFPlus.OccupancyDisclosure

theorem singleton_disclosure (C : Config) (es : List (Attempt C)) (r : Row C)
    (h : Honest (empty C) es) (hsingle : successful es = [r]) :
    recover (finalSnapshot es) = r.identifier := by sorry

end GBFPlus.OccupancyDisclosure
