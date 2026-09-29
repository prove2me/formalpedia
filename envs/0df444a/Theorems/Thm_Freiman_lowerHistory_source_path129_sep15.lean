-- Prove2me | Theorems.Thm_Freiman_lowerHistory_source_path129_sep15
-- name    : Freiman.lowerHistory_source_path129_sep15
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T15:55:54.645412+00:00
-- url     : https://prove2.me/theorems/12d6f7f6-572e-4979-a67a-12c043cf994d
-- title:
--   Exact source alternatives for left-history path 129
-- statement:
--   The source alternatives of the original left-history path with identifier 129 equal the explicitly listed certificate-bound lists, in their original order and with their original multiplicities. The formal statement specifies the path and the lists of indices in full. This identity supplies the source data in the original history-binding condition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_source_path129_sep15 : lowerHistorySourcePremises (⟨.left,129,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,16⟩ : LowerHistoryPath) =
    ([[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136]] : List (List Nat)).map (List.map lowerHistoryBound) := by sorry
